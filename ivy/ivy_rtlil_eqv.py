#! /usr/bin/env python
#
# rtlil_eqv -- combinational equivalence checker for RTLIL (.il) designs.
#
# Given two single-clocked designs with an active-low synchronous reset,
# whose inputs, outputs and registers match one-to-one by name (except for
# the clock and reset, which are named per design in the config), this tool
# checks that the logic cone of every corresponding output and register is
# combinationally equivalent between the two designs.  Registers are treated
# as cut points: their current-state values are free inputs and their
# next-state functions are the cones being compared.  This makes the check
# state-independent (it ignores reachability and initial values), which is
# exactly what "combinational equivalence" means here.
#
# Approach (see doc/projects/comb_equiv.md):
#   1. yosys converts each .il to an AIGER file (+ a name map).  Flip-flops
#      become AIGER latches (uninitialized), i.e. cut points.
#   2. We parse both AIGERs, check that the input/output/register names match
#      one-to-one, and build a name-matched combinational miter AIG in which
#      every corresponding cone pair is XOR'd and OR-reduced to a single
#      "bad" output.
#   3. abc proves the miter UNSAT (equivalent) or returns a counterexample,
#      which we simulate to report the offending cone(s) and input values.

import sys
import os
import subprocess
import time
import tempfile
import shutil

# --------------------------------------------------------------------------
# Locating the external tools (yosys, abc, and the aiger utilities).
# --------------------------------------------------------------------------

def _repo_root():
    # this file is <root>/ivy/ivy_rtlil_eqv.py
    return os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

def _find_tool(name, env, candidates):
    v = os.environ.get(env)
    if v:
        if os.path.isfile(v) and os.access(v, os.X_OK):
            return v
        sys.exit("error: %s=%s is not an executable" % (env, v))
    for c in candidates:
        if c and os.path.isfile(c) and os.access(c, os.X_OK):
            return c
    w = shutil.which(name)
    if w:
        return w
    sys.exit("error: could not find '%s' (set %s to its path)" % (name, env))

def tools():
    root = _repo_root()
    yosys = _find_tool('yosys', 'IVY_YOSYS', [])
    abc = _find_tool('abc', 'IVY_ABC',
                     [os.path.join(root, 'submodules', 'abc', 'abc')])
    aiger_dir = os.environ.get('IVY_AIGER',
                               os.path.join(root, 'submodules', 'aiger'))
    aigtoaig = os.path.join(aiger_dir, 'aigtoaig')
    if not (os.path.isfile(aigtoaig) and os.access(aigtoaig, os.X_OK)):
        aigtoaig = _find_tool('aigtoaig', 'IVY_AIGTOAIG', [])
    return yosys, abc, aigtoaig


# --------------------------------------------------------------------------
# Config file (.ileq): two INI-style sections [gold] and [gate], each with
#   file = <name>.il
#   top  = <module>
#   clk  = <clock input name>
#   rst  = <reset input name>
# --------------------------------------------------------------------------

class DesignCfg(object):
    def __init__(self, section):
        self.section = section
        self.file = None
        self.top = None
        self.clk = None
        self.rst = None

def parse_config(path):
    try:
        import configparser
    except ImportError:
        import ConfigParser as configparser
    cp = configparser.ConfigParser()
    # keep key case as written
    cp.optionxform = str
    try:
        with open(path) as f:
            cp.read_file(f)
    except IOError as e:
        sys.exit("error: cannot read config file '%s': %s" % (path, e))
    except configparser.Error as e:
        sys.exit("error: malformed config file '%s': %s" % (path, e))

    cfgdir = os.path.dirname(os.path.abspath(path))
    designs = []
    for sect in ('gold', 'gate'):
        if not cp.has_section(sect):
            sys.exit("error: config is missing required section [%s]" % sect)
        d = DesignCfg(sect)
        for key in ('file', 'top', 'clk', 'rst'):
            if not cp.has_option(sect, key):
                sys.exit("error: section [%s] is missing required key '%s'"
                         % (sect, key))
            setattr(d, key, cp.get(sect, key).strip())
        if not os.path.isabs(d.file):
            d.file = os.path.join(cfgdir, d.file)
        if not os.path.isfile(d.file):
            sys.exit("error: [%s] file '%s' does not exist" % (sect, d.file))
        designs.append(d)
    return designs[0], designs[1]


# --------------------------------------------------------------------------
# Running yosys to normalize a design and emit AIGER + map.
# --------------------------------------------------------------------------

YOSYS_SCRIPT = """
read_rtlil {il}
hierarchy -check -top {top}
proc
flatten
memory_map
async2sync
dfflegalize -cell $_DFF_P_ x
simplemap
setundef -zero
aigmap
write_aiger -map {mapf} {aigf}
"""

def run_yosys(yosys, cfg, workdir):
    aigf = os.path.join(workdir, cfg.section + ".aig")
    mapf = os.path.join(workdir, cfg.section + ".map")
    logf = os.path.join(workdir, cfg.section + ".yslog")
    script = YOSYS_SCRIPT.format(il=cfg.file, top=cfg.top,
                                 mapf=mapf, aigf=aigf)
    scriptf = os.path.join(workdir, cfg.section + ".ys")
    with open(scriptf, 'w') as f:
        f.write(script)
    with open(logf, 'w') as log:
        r = subprocess.call([yosys, '-q', '-s', scriptf],
                            stdout=log, stderr=subprocess.STDOUT)
    if r != 0:
        with open(logf) as log:
            tail = log.read()
        sys.exit("error: yosys failed on [%s] design '%s':\n%s"
                 % (cfg.section, cfg.file, tail))
    return aigf, mapf


# --------------------------------------------------------------------------
# Parsing AIGER (via ascii aag) + the yosys name map.
# --------------------------------------------------------------------------

class Design(object):
    def __init__(self, cfg):
        self.cfg = cfg
        self.maxvar = 0
        # (name,bit) -> literal   (all primary inputs, incl clk/rst)
        self.inputs = {}
        # (name,bit) -> literal
        self.outputs = {}
        # (name,bit) -> (cur_lit, next_lit)
        self.latches = {}
        # var -> (rhs0_lit, rhs1_lit)  (and gate whose output var is key)
        self.ands = {}
        # counts of AIGER signals with no public name (unmatchable)
        self.anon_inputs = 0
        self.anon_outputs = 0
        self.anon_latches = 0

def _strip_name(n):
    # yosys public names are emitted plain; strip a stray leading backslash.
    return n[1:] if n.startswith('\\') else n

def parse_map(mapf):
    ins, lats, outs = {}, {}, {}
    with open(mapf) as f:
        for line in f:
            parts = line.split()
            if len(parts) < 4:
                continue
            kind, idx, bit = parts[0], parts[1], parts[2]
            name = _strip_name(' '.join(parts[3:]))
            entry = (name, int(bit))
            if kind == 'input':
                ins[int(idx)] = entry
            elif kind == 'output':
                outs[int(idx)] = entry
            elif kind == 'latch':
                lats[int(idx)] = entry
    return ins, lats, outs

def parse_design(cfg, aigf, mapf, aigtoaig):
    aagf = aigf + '.aag'
    r = subprocess.call([aigtoaig, aigf, aagf])
    if r != 0:
        sys.exit("error: aigtoaig failed to convert '%s'" % aigf)
    with open(aagf) as f:
        lines = f.read().split('\n')

    hdr = lines[0].split()
    if len(hdr) < 6 or hdr[0] != 'aag':
        sys.exit("error: '%s' is not a valid ascii AIGER header" % aagf)
    M, I, L, O, A = (int(x) for x in hdr[1:6])

    d = Design(cfg)
    d.maxvar = M
    pos = 1
    in_lits = [int(lines[pos + i]) for i in range(I)]; pos += I
    lat_defs = []
    for i in range(L):
        p = lines[pos + i].split()
        cur, nxt = int(p[0]), int(p[1])
        lat_defs.append((cur, nxt))
    pos += L
    out_lits = [int(lines[pos + i]) for i in range(O)]; pos += O
    for i in range(A):
        p = lines[pos + i].split()
        lhs, r0, r1 = int(p[0]), int(p[1]), int(p[2])
        d.ands[lhs >> 1] = (r0, r1)
    pos += A

    # The yosys map lists a line per *named* AIGER position; a position may
    # carry several names (aliased public wires) or none (anonymous FF).  So
    # the map may have fewer, equal, or more lines than there are positions.
    ins, lats, outs = parse_map(mapf)

    for idx, (name, bit) in ins.items():
        if 0 <= idx < I:
            d.inputs[(name, bit)] = in_lits[idx]
    for idx, (name, bit) in lats.items():
        if 0 <= idx < L:
            d.latches[(name, bit)] = lat_defs[idx]
    for idx, (name, bit) in outs.items():
        if 0 <= idx < O:
            d.outputs[(name, bit)] = out_lits[idx]

    d.anon_inputs = I - len(set(ins))
    d.anon_outputs = O - len(set(outs))
    d.anon_latches = L - len(set(lats))
    return d


# --------------------------------------------------------------------------
# In-memory AIG builder for the miter.
# --------------------------------------------------------------------------

class AIG(object):
    def __init__(self):
        self.maxvar = 0
        self.ands = []          # list of (lhs_lit, r0_lit, r1_lit)
        self._cache = {}        # (a,b) -> lhs_lit, structural hashing

    def newvar(self):
        self.maxvar += 1
        return self.maxvar * 2

    def mk_and(self, a, b):
        if a == 0 or b == 0:
            return 0
        if a == 1:
            return b
        if b == 1:
            return a
        if a == b:
            return a
        if a == (b ^ 1):
            return 0
        key = (a, b) if a < b else (b, a)
        if key in self._cache:
            return self._cache[key]
        lhs = self.newvar()
        self.ands.append((lhs, key[0], key[1]))
        self._cache[key] = lhs
        return lhs

    def mk_not(self, a):
        return a ^ 1

    def mk_or(self, a, b):
        return self.mk_not(self.mk_and(self.mk_not(a), self.mk_not(b)))

    def mk_xor(self, a, b):
        return self.mk_or(self.mk_and(a, self.mk_not(b)),
                          self.mk_and(self.mk_not(a), b))

    def write_aag(self, path, inputs, output, in_names=None):
        # inputs: list of PI literals (even, vars 1..I); output: literal
        with open(path, 'w') as f:
            f.write("aag %d %d 0 1 %d\n" %
                    (self.maxvar, len(inputs), len(self.ands)))
            for lit in inputs:
                f.write("%d\n" % lit)
            f.write("%d\n" % output)
            for (lhs, r0, r1) in self.ands:
                f.write("%d %d %d\n" % (lhs, r0, r1))
            if in_names:
                for i, nm in enumerate(in_names):
                    f.write("i%d %s\n" % (i, nm))
                f.write("o0 bad\n")


# --------------------------------------------------------------------------
# Miter construction.
# --------------------------------------------------------------------------

def canon_input_key(cfg, name, bit):
    # clock/reset get design-independent keys so they are paired across
    # the two designs even when named differently.
    if name == cfg.clk:
        return ('__clk__', bit)
    if name == cfg.rst:
        return ('__rst__', bit)
    return ('in', name, bit)

def check_match(gold, gate):
    """Verify inputs/outputs/registers match one-to-one by name."""
    errs = []

    def keyset_inputs(d):
        return set(canon_input_key(d.cfg, n, b) for (n, b) in d.inputs)

    # anonymous (unnamed) signals cannot be matched by name
    for d in (gold, gate):
        if d.anon_latches:
            errs.append("[%s] has %d register bit(s) with no public name "
                        "(cannot be matched); name them or optimize them away"
                        % (d.cfg.section, d.anon_latches))
        if d.anon_inputs:
            errs.append("[%s] has %d unnamed primary input bit(s)"
                        % (d.cfg.section, d.anon_inputs))
        if d.anon_outputs:
            errs.append("[%s] has %d unnamed primary output bit(s)"
                        % (d.cfg.section, d.anon_outputs))

    gset, tset = keyset_inputs(gold), keyset_inputs(gate)
    # clk / rst must exist in each design
    for d in (gold, gate):
        if not any(n == d.cfg.clk for (n, b) in d.inputs):
            errs.append("[%s] clock input '%s' not found among inputs"
                        % (d.cfg.section, d.cfg.clk))
        if not any(n == d.cfg.rst for (n, b) in d.inputs):
            errs.append("[%s] reset input '%s' not found among inputs"
                        % (d.cfg.section, d.cfg.rst))

    def report(kind, gs, ts):
        # group differing (name,bit) keys by base name for readability
        def summarize(diff, where):
            bits = {}
            for k in diff:
                # input keys are ('in',name,bit); out/reg keys are (name,bit)
                name, bit = (k[1], k[2]) if len(k) == 3 else k
                bits.setdefault(name, []).append(bit)
            for name in sorted(bits):
                bs = sorted(bits[name])
                rng = ("bit %d" % bs[0] if len(bs) == 1
                       else "%d bits [%d..%d]" % (len(bs), min(bs), max(bs)))
                errs.append("%s '%s' (%s) only in %s"
                            % (kind, name, rng, where))
        summarize(gs - ts, "gold")
        summarize(ts - gs, "gate")

    report("input", gset, tset)
    report("output", set(gold.outputs), set(gate.outputs))
    report("register", set(gold.latches), set(gate.latches))

    if errs:
        sys.exit("error: input/output/register match is incomplete:\n  "
                 + "\n  ".join(errs))

def build_miter(gold, gate):
    aig = AIG()

    # Shared primary inputs: union of matched inputs (incl clk/rst) and all
    # register current-state values.  Allocate them first so they occupy
    # vars 1..I of the miter AIG.
    in_keys = set()
    for d in (gold, gate):
        for (n, b) in d.inputs:
            in_keys.add(canon_input_key(d.cfg, n, b))
    reg_keys = set(('reg',) + k for k in gold.latches)

    pi_keys = sorted(in_keys) + sorted(reg_keys)
    pi_lit = {}
    pi_order = []          # list of (key, literal)
    for k in pi_keys:
        lit = aig.newvar()
        pi_lit[k] = lit
        pi_order.append((k, lit))

    def translate(design):
        # var -> positive global literal
        gmap = {0: 0}
        for (n, b), lit in design.inputs.items():
            gmap[lit >> 1] = pi_lit[canon_input_key(design.cfg, n, b)]
        for (n, b), (cur, nxt) in design.latches.items():
            gmap[cur >> 1] = pi_lit[('reg', n, b)]
        for lhs_var in sorted(design.ands):
            r0, r1 = design.ands[lhs_var]
            g0 = gmap[r0 >> 1] ^ (r0 & 1)
            g1 = gmap[r1 >> 1] ^ (r1 & 1)
            gmap[lhs_var] = aig.mk_and(g0, g1)
        return gmap

    gmap_g = translate(gold)
    gmap_t = translate(gate)

    def lit_of(gmap, lit):
        return gmap[lit >> 1] ^ (lit & 1)

    cones = []   # (label, diff_literal)
    for key in sorted(gold.outputs):
        n, b = key
        dl = aig.mk_xor(lit_of(gmap_g, gold.outputs[key]),
                        lit_of(gmap_t, gate.outputs[key]))
        cones.append(("output %s[%d]" % (n, b), dl))
    for key in sorted(gold.latches):
        n, b = key
        dl = aig.mk_xor(lit_of(gmap_g, gold.latches[key][1]),
                        lit_of(gmap_t, gate.latches[key][1]))
        cones.append(("reg %s[%d]" % (n, b), dl))

    bad = 0
    for _, dl in cones:
        bad = aig.mk_or(bad, dl)

    return aig, pi_order, bad, cones


# --------------------------------------------------------------------------
# Simulation for counterexample attribution.
# --------------------------------------------------------------------------

def simulate(aig, pi_order, cones, cex_bits):
    val = {0: 0}
    for i, (key, lit) in enumerate(pi_order):
        val[lit >> 1] = cex_bits[i] if i < len(cex_bits) else 0
    for (lhs, r0, r1) in aig.ands:
        a = val[r0 >> 1] ^ (r0 & 1)
        b = val[r1 >> 1] ^ (r1 & 1)
        val[lhs >> 1] = a & b

    def ev(lit):
        return val[lit >> 1] ^ (lit & 1)

    failing = [(label, dl) for (label, dl) in cones if ev(dl) == 1]

    # support (PI vars) of a literal, over the and-gate structure
    and_by_var = dict((lhs >> 1, (r0, r1)) for (lhs, r0, r1) in aig.ands)
    pi_vars = set(lit >> 1 for (_, lit) in pi_order)

    def support(lit):
        seen = set()
        out = set()
        stack = [lit >> 1]
        while stack:
            v = stack.pop()
            if v in seen:
                continue
            seen.add(v)
            if v in pi_vars:
                out.add(v)
            elif v in and_by_var:
                r0, r1 = and_by_var[v]
                stack.append(r0 >> 1)
                stack.append(r1 >> 1)
        return out

    var_key = dict((lit >> 1, key) for (key, lit) in pi_order)
    return failing, support, var_key, val


def key_label(key):
    if key[0] == '__clk__':
        return "clk"
    if key[0] == '__rst__':
        return "rst"
    if key[0] == 'in':
        return "%s[%d]" % (key[1], key[2])
    if key[0] == 'reg':
        return "%s[%d] (state)" % (key[1], key[2])
    return str(key)


# --------------------------------------------------------------------------
# abc invocation.
# --------------------------------------------------------------------------

def run_abc(abc, aigtoaig, aig, pi_order, bad, workdir):
    aagf = os.path.join(workdir, "miter.aag")
    aigf = os.path.join(workdir, "miter.aig")
    cexf = os.path.join(workdir, "miter.cex")
    in_names = [key_label(k) for (k, _) in pi_order]
    aig.write_aag(aagf, [lit for (_, lit) in pi_order], bad, in_names)
    r = subprocess.call([aigtoaig, aagf, aigf])
    if r != 0:
        sys.exit("error: aigtoaig failed to binarize the miter")

    cmd = "read %s; sat; write_cex -a %s" % (aigf, cexf)
    out = subprocess.check_output([abc, '-c', cmd],
                                  stderr=subprocess.STDOUT).decode()
    if 'UNSATISFIABLE' in out:
        return None
    if 'SATISFIABLE' not in out:
        sys.exit("error: unexpected abc output:\n%s" % out)
    bits = []
    try:
        with open(cexf) as f:
            for ch in f.read():
                if ch in '01':
                    bits.append(int(ch))
    except IOError:
        sys.exit("error: abc reported SAT but wrote no counterexample")
    return bits


# --------------------------------------------------------------------------
# Main.
# --------------------------------------------------------------------------

def main():
    args = sys.argv[1:]
    if len(args) != 1:
        sys.stderr.write("usage: rtlil_eqv <config>.ileq\n")
        return 2
    config = args[0]

    yosys, abc, aigtoaig = tools()
    gold_cfg, gate_cfg = parse_config(config)

    t0 = time.time()
    workdir = tempfile.mkdtemp(prefix="rtlil_eqv_")
    keep = os.environ.get('IVY_RTLIL_EQV_KEEP')
    try:
        g_aig, g_map = run_yosys(yosys, gold_cfg, workdir)
        t_aig, t_map = run_yosys(yosys, gate_cfg, workdir)
        gold = parse_design(gold_cfg, g_aig, g_map, aigtoaig)
        gate = parse_design(gate_cfg, t_aig, t_map, aigtoaig)

        check_match(gold, gate)

        aig, pi_order, bad, cones = build_miter(gold, gate)
        cex = run_abc(abc, aigtoaig, aig, pi_order, bad, workdir)
        elapsed = time.time() - t0

        if cex is None:
            print("compared %d cones (%d outputs, %d registers) in %.2fs"
                  % (len(cones), len(gold.outputs), len(gold.latches),
                     elapsed))
            print("OK")
            return 0

        # miscompare: attribute to cone(s)
        failing, support, var_key, val = simulate(aig, pi_order, cones, cex)
        print("NOT EQUIVALENT: %d of %d cones differ\n"
              % (len(failing), len(cones)))
        shown = failing[:20]
        for (label, dl) in shown:
            print("cone: %s" % label)
            supp = support(dl)
            for v in sorted(supp, key=lambda v: key_label(var_key[v])):
                print("    %-28s = %d" % (key_label(var_key[v]), val[v]))
            print("")
        if len(failing) > len(shown):
            print("... and %d more differing cones" % (len(failing) - len(shown)))
        return 1
    finally:
        if keep:
            sys.stderr.write("[rtlil_eqv] work dir kept: %s\n" % workdir)
        else:
            shutil.rmtree(workdir, ignore_errors=True)


if __name__ == "__main__":
    sys.exit(main())
