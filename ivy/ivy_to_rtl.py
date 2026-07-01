#! /usr/bin/env python
#
# Copyright (c) Microsoft Corporation. All Rights Reserved.
#
# Translate an Ivy hardware description into Yosys RTLIL.
#
# See doc/projects/ivy_to_rtl.md for the design. The command
#
#     ivy_to_rtl <file>.ivy
#
# writes the elaborated netlist to <file>.il in the current directory.

from . import ivy_init
from . import ivy_logic as il
from . import ivy_module as im
from . import ivy_utils as iu
from . import ivy_actions as ia
from . import ivy_ast
from . import logic as lg
from . import ivy_transrel as tr
from . import ivy_compiler as ic
from . import ivy_isolate as iso
import sys
import re

from collections import defaultdict


# ----------------------------------------------------------------------------
# Sorts and bit widths
#
# Hardware wires/state may have one of the interpreted types allowed in
# hardware descriptions: bool (1 bit) or bv[k] (k bits). Arrays (bv[j]->bv[k])
# are not yet handled. An Ivy sort is interpreted via mod.sig.interp, which
# maps the sort name to a string such as 'bv[8]'.

_bv_re = re.compile(r'^bv\[(\d+)\]$')

def sort_width(sort):
    """Bit width of an interpreted sort; error on an unsupported type."""
    if il.is_boolean_sort(sort):
        return 1
    name = getattr(sort, 'name', None)
    interp = il.sig.interp.get(name) if name is not None else None
    if isinstance(interp, str):
        m = _bv_re.match(interp)
        if m:
            return int(m.group(1))
        if interp == 'bool':
            return 1
    raise iu.IvyError(None,
        "unsupported type in hardware description: {}".format(sort))

def is_array_sort(sort):
    """True if sort is an array/function sort dom -> rng (a memory)."""
    return hasattr(sort, 'dom') and len(sort.dom) >= 1

def array_dims(sort):
    """(address width, data width) of a single-dimension array sort."""
    if len(sort.dom) != 1:
        raise iu.IvyError(None,
            "only one-dimensional arrays are supported: {}".format(sort))
    return sort_width(sort.dom[0]), sort_width(sort.rng)


# ----------------------------------------------------------------------------
# RTLIL identifiers and constants
#
# RTLIL public identifiers begin with '\' and automatic (internal) ones with
# '$'; both may contain dots, so we can reuse Ivy symbol names verbatim.

def pub_id(name):
    return '\\' + name

def mem_id(name):
    """A memory id as an RTLIL string literal, e.g. \\rf -> "\\rf"."""
    return '"\\\\' + name + '"'

def rtlil_const(value, width):
    bits = format(value & ((1 << width) - 1), '0{}b'.format(width))
    return "{}'{}".format(width, bits)


# ----------------------------------------------------------------------------
# Name helpers

def conj(enable, cond):
    """Conjoin a guard onto an (optional) enable term."""
    return cond if enable is None else il.And(enable, cond)

def strip_state_prefix(name):
    """Remove the transition-relation 'new_'/'__m_' (post/mid) prefixes. A wire
    is frozen during an action, so every copy denotes the same combinational
    value, i.e. the base wire."""
    changed = True
    while changed:
        changed = False
        for p in ('new_', '__m_'):
            if name.startswith(p):
                name = name[len(p):]
                changed = True
    return name

def parent_name(name):
    return name.rsplit('.', 1)[0] if '.' in name else 'this'

def compose(obj, k):
    return k if obj == 'this' else obj + '.' + k

def local_name(obj, name):
    """Name of a symbol relative to object obj."""
    if obj == 'this':
        return name
    prefix = obj + '.'
    return name[len(prefix):] if name.startswith(prefix) else name


# ----------------------------------------------------------------------------
# A single RTLIL module under construction

class Module(object):
    def __init__(self, name):
        self.name = name
        self.header = []     # wire declarations
        self.body = []       # cells and connections
        self.wires = {}      # id -> width
        self.port_idx = 0
        self.net_n = 0

    def add_wire(self, ident, width, direction=None):
        if ident in self.wires:
            return ident
        self.wires[ident] = width
        opts = ''
        if width != 1:
            opts += ' width {}'.format(width)
        if direction is not None:
            self.port_idx += 1
            opts += ' {} {}'.format(direction, self.port_idx)
        self.header.append('  wire{} {}'.format(opts, ident))
        return ident

    def new_net(self, width):
        self.net_n += 1
        return self.add_wire('$' + str(self.net_n), width)

    def fresh(self, prefix):
        self.net_n += 1
        return '{}${}'.format(prefix, self.net_n)

    def memory(self, name, width, size):
        self.header.append('  memory width {} size {} {}'.format(
            width, size, name))

    def connect(self, lhs, rhs):
        self.body.append('  connect {} {}'.format(lhs, rhs))

    def emit(self, line):
        self.body.append(line)

    def cell(self, celltype, name, params, conns):
        self.body.append('  cell {} {}'.format(celltype, name))
        for k, v in params:
            self.body.append('    parameter {} {}'.format(k, v))
        for k, v in conns:
            self.body.append('    connect {} {}'.format(k, v))
        self.body.append('  end')

    def to_str(self):
        return ('module {}\n'.format(pub_id(self.name))
                + '\n'.join(self.header + self.body)
                + '\nend\n')


# ----------------------------------------------------------------------------
# Expression translation context

class Ctx(object):
    """Context for translating an expression into nets in module `m`,
    interpreting the symbols of object `obj`. `local_defs` maps the names of
    locally-defined intermediate symbols (the `new_*` and `__*` symbols of an
    action update) to their defining Definition; these get materialized as
    internal nets. Plain wire/state references become net ids directly."""
    def __init__(self, trans, m, obj, local_defs=None):
        self.trans = trans
        self.m = m
        self.obj = obj
        self.local_defs = local_defs or {}
        self.cache = {}


# ----------------------------------------------------------------------------
# The translator

RESET = 'rst'   # global reset net name

class Translator(object):
    def __init__(self, mod):
        self.mod = mod
        self.modules = []
        # wire definitions, indexed by the symbol they define
        self.wire_defs = {}              # symbol -> rhs term
        self.def_owner = {}              # defined symbol name -> owning object
        for ldf in mod.definitions:
            if self.is_spec(str(ldf.label)) if ldf.label is not None else False:
                continue
            sym = ldf.formula.args[0].rep
            self.wire_defs[sym] = ldf.formula.args[1]
            if ldf.label is not None:
                self.def_owner[sym.name] = parent_name(str(ldf.label))
        self.objects = set(mod.hierarchy.keys())
        self.wire_by_name = dict((s.name, s) for s in mod.wires)
        self._update_cache = {}
        self.compute_state()
        self.top = self.top_object()
        self.compute_has_state()

    # -- specification filtering --------------------------------------------

    def has_attr(self, name, attr):
        """True if name or any ancestor carries the given attribute."""
        parts = name.split('.')
        for i in range(len(parts), 0, -1):
            if '.'.join(parts[:i]) + '.' + attr in self.mod.attributes:
                return True
        return False

    def is_spec(self, name):
        """True if name or any ancestor carries the 'spec' attribute."""
        return self.has_attr(name, 'spec')

    def is_spec_only(self, obj):
        """True if every member of obj is specification code. Such an object
        (e.g. an abstract model written inside `specification { ... }`) is not
        part of the hardware and is excluded from the netlist, even though the
        isolate name itself carries no 'spec' attribute."""
        members = self.mod.hierarchy.get(obj, set())
        if not members:
            return self.is_spec(obj)
        for k in members:
            full = compose(obj, k)
            if full in self.objects:
                if not self.is_spec_only(full):
                    return False
            elif not self.is_spec(full):
                return False
        return True

    def in_design(self, obj):
        """True if obj is a hardware module of the design, as opposed to a
        specification, a shared theory/library object, or a type."""
        if obj == 'this':
            return False
        if self.is_spec(obj) or self.is_spec_only(obj) or self.has_attr(obj, 'global'):
            return False
        if obj in il.sig.sorts:
            return False
        return True

    def is_descendant(self, owner, obj):
        """True if object `owner` lies within object `obj` (everything lies
        within the global scope 'this')."""
        if obj == 'this':
            return True
        return owner == obj or owner.startswith(obj + '.')

    # -- hierarchy helpers --------------------------------------------------

    def children(self, obj):
        kids = self.mod.hierarchy.get(obj, set())
        return sorted(c for c in (compose(obj, k) for k in kids)
                      if c in self.objects and self.in_design(c))

    def owning_object(self, name):
        """The object in which a symbol/action `name` is declared: the longest
        object-name prefix."""
        best = None
        for obj in self.objects:
            if obj == 'this':
                continue
            if name == obj or name.startswith(obj + '.'):
                if best is None or len(obj) > len(best):
                    best = obj
        return best if best is not None else 'this'

    def root_objects(self):
        return self.children('this')

    # -- state and updates --------------------------------------------------

    def compute_state(self):
        # Clocks are the actions exported to the environment; each becomes a
        # clock wire. The implicit 'init' action is the global reset. The RTL
        # is generated from the register updates, which are the 'after' mixins
        # into these actions. Mixers into any other action (e.g. library
        # function implementations) are specification/non-clock code and are
        # simply ignored. The only soundness requirement is that the mixers
        # into the exported actions are all 'after' mixins; a 'before' or
        # 'implement' mixin there would mean we are dropping code that runs in
        # the clocked action, so the RTL would not be a safe substitution.
        self.clocks = sorted(set(e.exported() for e in self.mod.exports)
                             - {'init'})
        self.obj_mixers = defaultdict(lambda: defaultdict(list))
        for mixee in list(self.clocks) + ['init']:
            for mx in self.mod.mixins.get(mixee, []):
                mixer = mx.mixer()
                if self.is_spec(mixer):
                    continue   # e.g. the state update of an abstract model
                if not isinstance(mx, ivy_ast.MixinAfterDef):
                    raise iu.IvyError(None,
                        "'{}' mixes into the exported action '{}' but is not "
                        "an 'after' mixin; the RTL would not be a safe "
                        "substitution".format(mixer, mixee))
                self.obj_mixers[self.owning_object(mixer)][mixee].append(mixer)

        # state variables updated by each object (post minus wires)
        self.state_vars = defaultdict(list)
        for obj in self.obj_mixers:
            seen = set()
            for mixee in self.obj_mixers[obj]:
                upd = self.get_update(obj, mixee)
                if upd is None:
                    continue
                for s in upd[0]:
                    if s.name not in seen:
                        seen.add(s.name)
                        self.state_vars[obj].append(s)

    def top_object(self):
        """The root module of the design: the object owning the top-level
        import/export wires. With no such wires, a single root object, else the
        global scope 'this'."""
        io = list(self.mod.input_wires) + list(self.mod.output_wires)
        owners = set(self.owning_object(s.name) for s in io)
        if len(owners) == 1:
            return owners.pop()
        roots = self.root_objects()
        return roots[0] if len(roots) == 1 else 'this'

    def compute_has_state(self):
        # transitive has-state, from the top module down
        self.has_state_set = set()
        def visit(obj):
            res = bool(self.state_vars.get(obj))
            for c in self.children(obj):
                res = visit(c) or res
            if res:
                self.has_state_set.add(obj)
            return res
        visit(self.top)

    def get_update(self, obj, mixee):
        """Return (state_syms, trans, defidx) for object obj on mixee, or
        None if obj has no mixers for that mixee."""
        key = (obj, mixee)
        if key in self._update_cache:
            return self._update_cache[key]
        mixers = self.obj_mixers[obj].get(mixee, [])
        if not mixers:
            self._update_cache[key] = None
            return None
        actions = [self.mod.actions[name] for name in mixers]
        seq = ia.Sequence(*actions)
        updated, trans, _ = seq.update(self.mod, None)
        state = [s for s in updated if s not in self.mod.wires]
        # detect interference: a state var updated here owned by another object
        for s in state:
            if self.owning_object(s.name) != obj:
                raise iu.IvyError(None,
                    "interference: object {} updates {} owned by {}".format(
                        obj, s.name, self.owning_object(s.name)))
        defidx = dict((d.defines().name, d) for d in trans.defs)
        res = (state, trans, defidx)
        self._update_cache[key] = res
        return res

    # -- wire classification ------------------------------------------------

    def module_wires(self, obj):
        return [w for w in self.mod.wires if self.owning_object(w.name) == obj]

    def references(self, obj):
        """Names of symbols referenced by definitions/updates owned by obj."""
        names = set()
        for sym, rhs in self.wire_defs.items():
            if self.def_owner.get(sym.name) == obj:
                names.update(s.name for s in used_symbols(rhs))
        for mixee in self.obj_mixers.get(obj, {}):
            upd = self.get_update(obj, mixee)
            if upd:
                for d in upd[1].defs:
                    names.update(s.name for s in used_symbols(d.args[1]))
        return names

    def classify(self, obj):
        """Return (inputs, outputs, internals) lists of the wire symbols owned
        by obj. Foreign wires referenced from obj (a sibling's output, say) are
        not owned by obj; see foreign_inputs."""
        is_top = (obj == self.top)
        input_names = set(s.name for s in self.mod.input_wires)
        output_names = set(s.name for s in self.mod.output_wires)
        # for a non-top module, an owned wire defined inside obj is an output
        # iff it is referenced by the parent (otherwise it is internal)
        prefs = self.references(parent_name(obj)) if not is_top else set()
        inputs, outputs, internals = [], [], []
        for w in self.module_wires(obj):
            d = self.def_owner.get(w.name)
            if is_top:
                if w.name in input_names:
                    inputs.append(w)
                elif w.name in output_names:
                    outputs.append(w)
                else:
                    internals.append(w)
            elif d == obj:
                outputs.append(w) if w.name in prefs else internals.append(w)
            else:
                inputs.append(w)
        inputs.sort(key=lambda s: s.name)
        outputs.sort(key=lambda s: s.name)
        return inputs, outputs, internals

    def foreign_inputs(self, obj):
        """Wires referenced by obj's logic but owned by an object outside obj
        (e.g. a sibling's output). Per the doc's implicit-I/O rule, such a wire
        is an input of obj, wired up by the parent."""
        res, seen = [], set()
        for name in self.references(obj):
            if name in self.wire_by_name and name not in seen:
                owner = self.owning_object(name)
                if owner != obj and not self.is_descendant(owner, obj):
                    seen.add(name)
                    res.append(self.wire_by_name[name])
        return sorted(res, key=lambda s: s.name)

    # -- top-level driver ---------------------------------------------------

    def translate(self):
        self.emit_object(self.top)
        header = '# Generated by ivy_to_rtl from {}\n\nautoidx 1\n\n'.format(
            self.mod.name + '.ivy')
        return header + '\n'.join(m.to_str() for m in self.modules)

    # -- per-object emission ------------------------------------------------

    def emit_object(self, obj):
        m = Module(obj)
        inputs, outputs, internals = self.classify(obj)
        foreign = self.foreign_inputs(obj)

        # declare data ports (named connections make the numbering cosmetic)
        for w in inputs + foreign:
            m.add_wire(pub_id(local_name(obj, w.name)), sort_width(w.sort), 'input')
        for w in outputs:
            m.add_wire(pub_id(local_name(obj, w.name)), sort_width(w.sort), 'output')
        # clock and reset ports for modules that contain state
        if obj in self.has_state_set:
            for c in self.clocks:
                m.add_wire(pub_id(c), 1, 'input')
            m.add_wire(pub_id(RESET), 1, 'input')
        # internal wires
        for w in internals:
            m.add_wire(pub_id(local_name(obj, w.name)), sort_width(w.sort))

        ctx = Ctx(self, m, obj)

        # child input ports: a wire of a child defined by a definition in obj
        child_set = set(self.children(obj))
        child_input_def = {}     # child input wire name -> rhs term
        for sym, rhs in self.wire_defs.items():
            if self.def_owner.get(sym.name) != obj:
                continue
            owner = self.owning_object(sym.name)
            if owner in child_set:
                child_input_def[sym.name] = rhs

        # instantiate child cells
        for c in self.children(obj):
            self.emit_child_cell(m, ctx, obj, c, child_input_def)

        # combinational definitions whose lhs is a wire of obj
        for w in outputs + internals:
            if w in self.wire_defs and self.def_owner.get(w.name) == obj:
                val = self.emit_expr(ctx, self.wire_defs[w])
                m.connect(pub_id(local_name(obj, w.name)), val)

        # scalar state variables -> D flip-flops with synchronous reset
        for v in self.state_vars.get(obj, []):
            if not is_array_sort(v.sort):
                self.emit_dff(m, obj, v)

        # array state variables and read-only arrays -> memories
        for arr in self.memories(obj):
            self.emit_memory(m, ctx, obj, arr)

        self.modules.append(m)
        for c in self.children(obj):
            self.emit_object(c)

    def emit_child_cell(self, m, ctx, obj, c, child_input_def):
        cinputs, coutputs, _ = self.classify(c)
        conns = []
        for w in cinputs:
            rhs = child_input_def.get(w.name)
            port = pub_id(local_name(c, w.name))
            if rhs is None:
                # undriven child input; leave a dangling net
                net = m.new_net(sort_width(w.sort))
                conns.append((port, net))
            else:
                conns.append((port, self.emit_expr(ctx, rhs)))
        # foreign inputs of the child are driven, by name, from the net in obj
        # carrying that wire (e.g. a sibling's output)
        for w in self.foreign_inputs(c):
            net = pub_id(local_name(obj, w.name))
            m.add_wire(net, sort_width(w.sort))
            conns.append((pub_id(local_name(c, w.name)), net))
        for w in coutputs:
            net = pub_id(local_name(obj, w.name))
            m.add_wire(net, sort_width(w.sort))
            conns.append((pub_id(local_name(c, w.name)), net))
        if c in self.has_state_set:
            for clk in self.clocks:
                conns.append((pub_id(clk), pub_id(clk)))
            conns.append((pub_id(RESET), pub_id(RESET)))
        m.cell(pub_id(c), pub_id(local_name(obj, c)), [], conns)

    def emit_dff(self, m, obj, v):
        width = sort_width(v.sort)
        qnet = m.add_wire(pub_id(local_name(obj, v.name)), width)
        newsym = tr.new(v)

        # the action (clock) update value
        clk_used, dval = None, None
        for clk in self.clocks:
            upd = self.get_update(obj, clk)
            if upd and newsym.name in upd[2]:
                cctx = Ctx(self, m, obj, upd[2])
                dval = self.emit_expr(cctx, upd[2][newsym.name].args[1])
                clk_used = clk
                break
        if dval is None:
            dval = qnet  # no clocked update: hold value

        # the reset value, from the 'init' update
        rstval = rtlil_const(0, width)
        init = self.get_update(obj, 'init')
        if init and newsym.name in init[2]:
            ictx = Ctx(self, m, obj, init[2])
            rstval = self.emit_expr(ictx, init[2][newsym.name].args[1])

        # D = rst ? rstval : dval
        dnet = m.new_net(width)
        m.cell('$mux', '$mux$' + v.name,
               [('\\WIDTH', width)],
               [('\\A', dval), ('\\B', rstval), ('\\S', pub_id(RESET)),
                ('\\Y', dnet)])
        # Q register
        clk_net = pub_id(clk_used) if clk_used else pub_id(self.clocks[0])
        m.cell('$dff', '$dff$' + v.name,
               [('\\WIDTH', width), ('\\CLK_POLARITY', 1)],
               [('\\CLK', clk_net), ('\\D', dnet), ('\\Q', qnet)])

    # -- memories -----------------------------------------------------------

    def memories(self, obj):
        """Array-valued symbols owned by obj that are updated or read: these
        become RTLIL memories."""
        syms = {}
        for v in self.state_vars.get(obj, []):
            if is_array_sort(v.sort):
                syms[v.name] = v
        def scan(term):
            if self.is_array_ref(term) and self.owning_object(term.rep.name) == obj:
                syms[term.rep.name] = term.rep
            for a in term.args:
                scan(a)
        for sym, rhs in self.wire_defs.items():
            if self.def_owner.get(sym.name) == obj:
                scan(rhs)
        for mixee in self.obj_mixers.get(obj, {}):
            upd = self.get_update(obj, mixee)
            if upd:
                for d in upd[1].defs:
                    scan(d.args[1])
        return [syms[k] for k in sorted(syms)]

    def emit_memory(self, m, ctx, obj, arr):
        aw, dw = array_dims(arr.sort)
        memname = local_name(obj, arr.name)
        m.memory(pub_id(memname), dw, 1 << aw)
        newsym = tr.new(arr)

        if self.get_update(obj, 'init') and \
           newsym.name in (self.get_update(obj, 'init')[2] or {}):
            raise iu.IvyError(None,
                "reset of array '{}' is not yet supported".format(arr.name))

        # gather the write ports contributed by each clock update
        clk_used, writes = None, []
        for clk in self.clocks:
            upd = self.get_update(obj, clk)
            if upd and newsym.name in upd[2]:
                if clk_used is not None:
                    raise iu.IvyError(None,
                        "array '{}' is written on more than one clock"
                        .format(arr.name))
                clk_used = clk
                d = upd[2][newsym.name]
                var = d.args[0].args[0]
                wctx = Ctx(self, m, obj, upd[2])
                self.collect_writes(d.args[1], arr, var, None, writes)
        if not writes:
            return   # a ROM: declared and read, never written

        # combine the (mutually exclusive) writes into one write port
        en_nets, addr_nets, data_nets = [], [], []
        for (en, addr, data) in writes:
            en_nets.append(self.emit_expr(wctx, en) if en is not None
                           else rtlil_const(1, 1))
            addr_nets.append(self.emit_expr(wctx, addr))
            data_nets.append(self.emit_expr(wctx, data))
        en = self.reduce_or(m, en_nets)
        addr = self.fold_mux(m, en_nets, addr_nets, aw)
        data = self.fold_mux(m, en_nets, data_nets, dw)
        en_wide = en if dw == 1 else '{ ' + ' '.join([en] * dw) + ' }'
        m.cell('$memwr_v2', m.fresh('$memwr$' + memname),
               [('\\MEMID', mem_id(memname)), ('\\ABITS', aw), ('\\WIDTH', dw),
                ('\\PORTID', 0), ('\\PRIORITY_MASK', "0'0"),
                ('\\CLK_ENABLE', "1'1"), ('\\CLK_POLARITY', "1'1")],
               [('\\ADDR', addr), ('\\DATA', data), ('\\EN', en_wide),
                ('\\CLK', pub_id(clk_used))])

    def collect_writes(self, expr, arr, var, enable, out):
        """Decompose a functional array-update body new_arr(var) = expr into a
        list of (enable, addr, data) point writes, appended to `out`. enable is
        an Ivy bool term (None means unconditional)."""
        if self.is_base_read(expr, arr, var):
            return
        if il.is_ite(expr):
            cond, then, els = expr.args
            if self.uses_var(cond, var):
                addr = self.eq_other_side(cond, var)
                if addr is None:
                    raise iu.IvyError(None,
                        "unsupported array index expression: {}".format(cond))
                out.append((enable, addr, then))
                self.collect_writes(els, arr, var, enable, out)
            else:
                self.collect_writes(then, arr, var, conj(enable, cond), out)
                self.collect_writes(els, arr, var,
                                    conj(enable, il.Not(cond)), out)
            return
        raise iu.IvyError(None,
            "unsupported array update (not a point write): {}".format(expr))

    def is_base_read(self, expr, arr, var):
        return (not il.is_constant(expr) and il.is_app(expr)
                and expr.rep.name == arr.name
                and len(expr.args) == 1 and expr.args[0] == var)

    def uses_var(self, expr, var):
        if expr == var:
            return True
        return any(self.uses_var(a, var) for a in expr.args)

    def eq_other_side(self, cond, var):
        # an index test may be wrapped in a single-conjunct And/Or
        while isinstance(cond, (lg.And, lg.Or)) and len(cond.args) == 1:
            cond = cond.args[0]
        if il.is_eq(cond):
            a, b = cond.args
            if a == var and not self.uses_var(b, var):
                return b
            if b == var and not self.uses_var(a, var):
                return a
        return None

    def reduce_or(self, m, nets):
        acc = nets[0]
        for n in nets[1:]:
            y = m.new_net(1)
            m.cell('$or', m.fresh('$or'),
                   [('\\A_SIGNED', 0), ('\\B_SIGNED', 0),
                    ('\\A_WIDTH', 1), ('\\B_WIDTH', 1), ('\\Y_WIDTH', 1)],
                   [('\\A', acc), ('\\B', n), ('\\Y', y)])
            acc = y
        return acc

    def fold_mux(self, m, sels, vals, width):
        """Combine value nets under mutually-exclusive selects into one net:
        later ports take precedence (irrelevant here, as selects are disjoint)."""
        acc = vals[0]
        for i in range(1, len(vals)):
            y = m.new_net(width)
            m.cell('$mux', m.fresh('$mux'),
                   [('\\WIDTH', width)],
                   [('\\A', acc), ('\\B', vals[i]), ('\\S', sels[i]),
                    ('\\Y', y)])
            acc = y
        return acc

    # -- expression translation ---------------------------------------------

    def emit_expr(self, ctx, term):
        m = ctx.m
        if il.is_numeral(term):
            return rtlil_const(int(term.name), sort_width(term.sort))
        if il.is_true(term):
            return rtlil_const(1, 1)
        if il.is_false(term):
            return rtlil_const(0, 1)
        if il.is_constant(term):
            name = term.name
            if name in ctx.cache:
                return ctx.cache[name]
            if name in ctx.local_defs:
                d = ctx.local_defs[name]
                val = self.emit_expr(ctx, d.args[1])
                net = m.new_net(sort_width(term.sort))
                m.connect(net, val)
                ctx.cache[name] = net
                return net
            return pub_id(local_name(ctx.obj, strip_state_prefix(name)))
        if il.is_ite(term):
            return self.emit_mux(ctx, term.args[0], term.args[1], term.args[2])
        if il.is_eq(term):
            return self.emit_cmp(ctx, '$eq', term.args[0], term.args[1])
        if isinstance(term, lg.Not):
            a = self.emit_expr(ctx, term.args[0])
            return self.emit_unary(ctx, '$not', a, 1)
        if isinstance(term, lg.And):
            return self.emit_reduce(ctx, '$and', term.args, rtlil_const(1, 1))
        if isinstance(term, lg.Or):
            return self.emit_reduce(ctx, '$or', term.args, rtlil_const(0, 1))
        if isinstance(term, lg.Implies):
            return self.emit_expr(ctx, lg.Or(lg.Not(term.args[0]), term.args[1]))
        if isinstance(term, lg.Iff):
            return self.emit_cmp(ctx, '$eq', term.args[0], term.args[1])
        if il.is_app(term):
            if self.is_array_ref(term):
                return self.emit_read(ctx, term)
            return self.emit_op(ctx, term)
        raise iu.IvyError(None, "cannot translate expression: {}".format(term))

    def is_array_ref(self, term):
        """True if term is a read of an array-valued state symbol (a memory),
        as opposed to an interpreted operator application."""
        return (il.is_app(term) and not il.is_constant(term)
                and is_array_sort(term.rep.sort)
                and self.in_design(self.owning_object(term.rep.name)))

    def emit_read(self, ctx, term):
        """Emit an asynchronous memory read port for term = arr(index)."""
        arr = term.rep
        aw, dw = array_dims(arr.sort)
        addr = self.emit_expr(ctx, term.args[0])
        data = ctx.m.new_net(dw)
        memname = local_name(ctx.obj, arr.name)
        ctx.m.cell('$memrd', ctx.m.fresh('$memrd$' + memname),
            [('\\MEMID', mem_id(memname)), ('\\ABITS', aw), ('\\WIDTH', dw),
             ('\\CLK_ENABLE', 0), ('\\CLK_POLARITY', 0), ('\\TRANSPARENT', 0)],
            [('\\CLK', "1'x"), ('\\EN', "1'x"), ('\\ADDR', addr),
             ('\\DATA', data)])
        return data

    _binops = {'+': '$add', '-': '$sub', '*': '$mul', '/': '$div'}

    def emit_op(self, ctx, term):
        op = term.rep.name
        if op in self._binops:
            return self.emit_arith(ctx, self._binops[op], term)
        if op.startswith('bfe['):
            return self.emit_bfe(ctx, op, term)
        if op == 'concat':
            return '{ ' + ' '.join(self.emit_expr(ctx, a) for a in term.args) + ' }'
        raise iu.IvyError(None, "unsupported operator: {}".format(op))

    def emit_arith(self, ctx, kind, term):
        m = ctx.m
        a = self.emit_expr(ctx, term.args[0])
        b = self.emit_expr(ctx, term.args[1])
        aw = sort_width(term.args[0].sort)
        bw = sort_width(term.args[1].sort)
        yw = sort_width(term.sort)
        y = m.new_net(yw)
        m.cell(kind, m_cell_name(kind, y),
               [('\\A_SIGNED', 0), ('\\B_SIGNED', 0),
                ('\\A_WIDTH', aw), ('\\B_WIDTH', bw), ('\\Y_WIDTH', yw)],
               [('\\A', a), ('\\B', b), ('\\Y', y)])
        return y

    def emit_cmp(self, ctx, kind, lhs, rhs):
        m = ctx.m
        a = self.emit_expr(ctx, lhs)
        b = self.emit_expr(ctx, rhs)
        aw = sort_width(lhs.sort)
        bw = sort_width(rhs.sort)
        y = m.new_net(1)
        m.cell(kind, m_cell_name(kind, y),
               [('\\A_SIGNED', 0), ('\\B_SIGNED', 0),
                ('\\A_WIDTH', aw), ('\\B_WIDTH', bw), ('\\Y_WIDTH', 1)],
               [('\\A', a), ('\\B', b), ('\\Y', y)])
        return y

    def emit_unary(self, ctx, kind, a, width):
        m = ctx.m
        y = m.new_net(width)
        m.cell(kind, m_cell_name(kind, y),
               [('\\A_SIGNED', 0), ('\\A_WIDTH', width), ('\\Y_WIDTH', width)],
               [('\\A', a), ('\\Y', y)])
        return y

    def emit_reduce(self, ctx, kind, args, identity):
        if not args:
            return identity
        acc = self.emit_expr(ctx, args[0])
        for a in args[1:]:
            b = self.emit_expr(ctx, a)
            m = ctx.m
            y = m.new_net(1)
            m.cell(kind, m_cell_name(kind, y),
                   [('\\A_SIGNED', 0), ('\\B_SIGNED', 0),
                    ('\\A_WIDTH', 1), ('\\B_WIDTH', 1), ('\\Y_WIDTH', 1)],
                   [('\\A', acc), ('\\B', b), ('\\Y', y)])
            acc = y
        return acc

    def emit_mux(self, ctx, cond, then, els):
        m = ctx.m
        s = self.emit_expr(ctx, cond)
        b = self.emit_expr(ctx, then)
        a = self.emit_expr(ctx, els)
        width = sort_width(then.sort)
        y = m.new_net(width)
        m.cell('$mux', m_cell_name('$mux', y),
               [('\\WIDTH', width)],
               [('\\A', a), ('\\B', b), ('\\S', s), ('\\Y', y)])
        return y

    def emit_bfe(self, ctx, op, term):
        mm = re.match(r'^bfe\[(\d+)\]\[(\d+)\]$', op)
        lo, hi = int(mm.group(1)), int(mm.group(2))
        a = self.emit_expr(ctx, term.args[0])
        if not a.startswith('\\') and not a.startswith('$'):
            # materialize so we can slice it
            net = ctx.m.new_net(sort_width(term.args[0].sort))
            ctx.m.connect(net, a)
            a = net
        return '{} [{}:{}]'.format(a, hi, lo) if hi != lo else '{} [{}]'.format(a, lo)


def m_cell_name(kind, ynet):
    return '{}{}'.format(kind, ynet)


def used_symbols(term):
    """All constant symbols (leaves) occurring in a term."""
    res = []
    def rec(t):
        if il.is_constant(t):
            res.append(t)
            return
        for a in t.args:
            rec(a)
    rec(term)
    return res


def main():
    iso.set_interpret_all_sorts(True)
    ic.set_verifying(False)
    ivy_init.read_params()
    iu.set_parameters({'coi':'false',
                       "create_imports":'true',
                       "enforce_axioms":'true',
                       'ui':'none',
                       'isolate_mode':'compile',
                       'assume_invariants':'false',
                       'keep_destructors':'true'})

    with im.Module():
        ivy_init.ivy_init(create_isolate=False)
        mod_name = im.module.name
        with iu.ErrorPrinter():
            trans = Translator(im.module)
            text = trans.translate()
        outfile = mod_name + '.il'
        with open(outfile, 'w') as f:
            f.write(text)
        sys.stderr.write('wrote {}\n'.format(outfile))


if __name__ == "__main__":
    main()
