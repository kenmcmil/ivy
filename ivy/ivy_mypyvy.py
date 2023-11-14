#
# Copyright (c) Microsoft Corporation. All Rights Reserved.
#
from . import ivy_actions
from . import ivy_logic as il
from . import ivy_module as im
from . import ivy_trace as it
from . import ivy_transrel as itr
from . import logic as lg
from . import mypyvy_syntax as pyv

logfile = None
verbose = False

# Ivy symbols have dots in them (due to the module system)
# but mypyvy doesn't allow dots in names, so we replace
# them with this string
DOT_REPLACEMENT = "_"
BRACE_REPLACEMENT = '_B_'
COLON_REPLACEMENT = "_c_"

# This is how Ivy internally represents true and false
_true = lg.And()
_false = lg.Or()

class Translation:
    '''Helper class for translating Ivy expressions to mypyvy expressions.'''
    def sort_type(ivy_sort):
        if il.is_function_sort(ivy_sort) and il.is_boolean_sort(ivy_sort.rng):
            return 'relation'
        elif il.is_function_sort(ivy_sort):
            return 'function'
        return 'individual'

    def to_pyv_sort(ivy_sort):
        if il.is_first_order_sort(ivy_sort) \
            or il.is_enumerated_sort(ivy_sort):
            return pyv.UninterpretedSort(ivy_sort.name)
        elif il.is_boolean_sort(ivy_sort):
            return pyv.BoolSort
        # Relation
        elif il.is_function_sort(ivy_sort) and il.is_boolean_sort(ivy_sort.rng):
            # FIXME: do we need the bool for rng?
            return tuple([Translation.to_pyv_sort(x) for x in ivy_sort.dom])
        elif il.is_function_sort(ivy_sort):
            return (tuple([Translation.to_pyv_sort(x) for x in ivy_sort.dom]), Translation.to_pyv_sort(ivy_sort.rng))
        else:
            raise NotImplementedError("translating sort {} to mypyvy ".format(repr(ivy_sort)))

    def to_pyv_name(ivy_name):
        if isinstance(ivy_name, str):
            name = ivy_name.replace(".", DOT_REPLACEMENT)
            name = name.replace('[', BRACE_REPLACEMENT)
            name = name.replace(']', BRACE_REPLACEMENT)
            name = name.replace(':', COLON_REPLACEMENT)
            return name
        raise Exception("cannot translate non-string name {} to mypyvy ".format(repr(ivy_name)))

    def translate_binders(binders) -> tuple[pyv.SortedVar]:
        '''Translate [var_name:var_sort] into mypyvy.'''
        vars = []
        for binder in binders:
            name = Translation.to_pyv_name(binder.name)
            sort = Translation.to_pyv_sort(binder.sort)
            vars.append(pyv.SortedVar(name, sort, None))
        return vars

    def translate_logic_fmla(fmla, is_twostate=False) -> pyv.Expr:
        '''Translates a logic formula (as defined in logic.py) to a
        mypyvy expression. (Note: these for some reason are not AST nodes.)'''

        if isinstance(fmla, lg.ForAll):
            # fmla.variables & fmla.body
            return pyv.Forall(Translation.translate_binders(fmla.variables), Translation.translate_logic_fmla(fmla.body, is_twostate))
        elif isinstance(fmla, lg.Exists):
            # fmla.variables & fmla.body
            return pyv.Exists(Translation.translate_binders(fmla.variables), Translation.translate_logic_fmla(fmla.body, is_twostate))
        elif isinstance(fmla, lg.Ite):
            # fmla.sort & fmla.cond & fmla.t_then, fmla.t_else
            return pyv.IfThenElse(Translation.translate_logic_fmla(fmla.cond, is_twostate), Translation.translate_logic_fmla(fmla.t_then, is_twostate), Translation.translate_logic_fmla(fmla.t_else, is_twostate))
        elif isinstance(fmla, lg.And):
            # fmla.terms
            if len(fmla.terms) == 0:
                return pyv.TrueExpr
            return pyv.And(*tuple([Translation.translate_logic_fmla(x, is_twostate) for x in fmla.terms]))
        elif isinstance(fmla, lg.Or):
            # fmla.terms
            if len(fmla.terms) == 0:
                return pyv.FalseExpr
            return pyv.Or(*tuple([Translation.translate_logic_fmla(x, is_twostate) for x in fmla.terms]))
        elif isinstance(fmla, lg.Eq):
            # fmla.t1 & fmla.t2
            return pyv.Eq(Translation.translate_logic_fmla(fmla.t1, is_twostate), Translation.translate_logic_fmla(fmla.t2, is_twostate))
        elif isinstance(fmla, lg.Implies):
            # fmla.t1 & fmla.t2
            return pyv.Implies(Translation.translate_logic_fmla(fmla.t1, is_twostate), Translation.translate_logic_fmla(fmla.t2, is_twostate))
        elif isinstance(fmla, lg.Iff):
            # fmla.t1 & fmla.t2
            return pyv.Iff(Translation.translate_logic_fmla(fmla.t1, is_twostate), Translation.translate_logic_fmla(fmla.t2, is_twostate))
        elif isinstance(fmla, lg.Not):
            # fmla.body
            return pyv.Not(Translation.translate_logic_fmla(fmla.body, is_twostate))
        elif isinstance(fmla, lg.Apply):
            # fmla.func & fmla.terms
            if is_twostate and itr.is_new(fmla.func):
                # We need to add a new() around the application and rename 'new_rel' to 'rel'
                old_name = itr.new_of(fmla.func).name
                fm = pyv.Apply(Translation.to_pyv_name(old_name), tuple([Translation.translate_logic_fmla(x, is_twostate) for x in fmla.terms]))
                return pyv.New(fm)
            else:
                return pyv.Apply(Translation.to_pyv_name(fmla.func.name), tuple([Translation.translate_logic_fmla(x, is_twostate) for x in fmla.terms]))
        elif isinstance(fmla, lg.Const):
            if is_twostate and itr.is_new(fmla):
                # We need to add a new() around the application and rename 'new_rel' to 'rel'
                old_name = itr.new_of(fmla).name
                fm = pyv.Id(Translation.to_pyv_name(old_name))
                return pyv.New(fm)
            return pyv.Id(Translation.to_pyv_name(fmla.name))
        elif isinstance(fmla, lg.Var):
            return pyv.Id(Translation.to_pyv_name(fmla.name))
        else:
            raise NotImplementedError("translating logic formula {} to mypyvy ".format(repr(fmla)))

    def globals_in_fmla(fmla) -> set[str]:
        '''Returns the set of global names that appear in a formula.
        We use this to mark constants/relations/functions as immutable
        if they appear in axioms.'''
        if isinstance(fmla, lg.ForAll) or isinstance(fmla, lg.Exists):
            return Translation.globals_in_fmla(fmla.body)
        elif isinstance(fmla, lg.Ite):
            return Translation.globals_in_fmla(fmla.cond) | Translation.globals_in_fmla(fmla.t_then) | Translation.globals_in_fmla(fmla.t_else)
        elif isinstance(fmla, lg.And) or isinstance(fmla, lg.Or):
            if len(fmla.terms) == 0:
                return set()
            return set.union(*[Translation.globals_in_fmla(x) for x in fmla.terms])
        elif isinstance(fmla, lg.Eq) or isinstance(fmla, lg.Implies) or isinstance(fmla, lg.Iff):
            return Translation.globals_in_fmla(fmla.t1) | Translation.globals_in_fmla(fmla.t2)
        elif isinstance(fmla, lg.Not):
            return Translation.globals_in_fmla(fmla.body)
        elif isinstance(fmla, lg.Apply):
            return {fmla.func.name} | set.union(*[Translation.globals_in_fmla(x) for x in fmla.terms])
        elif isinstance(fmla, lg.Const):
            return {fmla.name}
        elif isinstance(fmla, lg.Var):
            return set()
        else:
            raise NotImplementedError("constants_in_fmla: {}".format(repr(fmla)))

    def initializer_to_fmla(action: ivy_actions.Action) -> pyv.Expr:
        '''Translate an Ivy initializer to a mypyvy formula.'''
        # We want a one-state formula in this context
        upd = it.make_vc(action).to_formula()
        # For some reason, make_vc() returns a conjuction
        # that has Not(And()) at the end. We remove that.
        assert isinstance(upd, lg.And)
        upd = lg.And(*upd.terms[:-1])
        fmla = Translation.translate_logic_fmla(upd)
        return fmla

    def translate_action(name: str, action: ivy_actions.Action) -> pyv.DefinitionDecl:
        '''Translate an Ivy action to a mypyvy action.'''
        # This gives us a two-state formula
        (mod, tr, pre) = action.update(im.module,None)

        # Generate the modifies clauses
        modified = sorted([Translation.to_pyv_name(x.name) for x in mod])
        mods = tuple([pyv.ModifiesClause(x) for x in modified])

        # Sanity check: all modified variables should have new_ versions
        updated = sorted(list(set(filter(itr.is_new, tr.symbols()))))
        _updated_of = list(map(lambda x: Translation.to_pyv_name(itr.new_of(x).name), updated))
        assert modified == _updated_of, "modified != updated_of: {} != {}".format(modified, _updated_of)

        # Collect all implicitly existentially quantified variables
        # ...and add them as parameters to the transition after
        # the action's own formal params
        exs = sorted(list(set(filter(itr.is_skolem, tr.symbols()))))
        # it seems exs already contains action.formal_params
        # but we might to use action.formal_params to prettify names
        params = exs
        # TODO: what to do with action.formal_returns?
        # probably the easiest thing is to add them as existentials (parameters)

        # FIXME: we can get intermediate versions of relations and functions,
        # e.g. __m_l.a.b.balance.map(V0,V1), and we can't translate those as parameters

        # relation = old version
        # new_relation = new version
        # __fml:x = existentially quantified x
        # __new_fml:x = ???
        # __m_relation = temporary/modified version?

        # The precondition is defined negatively, i.e. the action *fails*
        # if the precondition is true, so we negate it.
        fmla = lg.And(lg.Not(pre.to_formula()), tr.to_formula())

        # Generate the transition
        pyv_name = Translation.to_pyv_name(name)
        pyv_params = Translation.translate_binders(params)
        pyv_fmla = Translation.translate_logic_fmla(fmla, is_twostate=True)

        trans = pyv.DefinitionDecl(True, 2, pyv_name, pyv_params, mods, pyv_fmla)
        return trans

# Our own class, which will be used to generate a mypyvy `Program`
class MypyvyProgram:
    # sort -> pyv.SortDecl
    # individual -> pyv.ConstantDecl (immutable)
    # axiom -> pyv.AxiomDecl

    def __init__(self):
        self.immutable_symbols = set()

        self.actions = []
        self.axioms = []
        self.constants = []
        self.functions = []
        self.initializers = []
        self.invariants = []
        self.relations = []
        self.sorts = []

    def add_constant_if_not_exists(self, cst):
        if cst.name not in [x.name for x in self.constants]:
            self.constants.append(cst)

    def add_sort(self, sort):
        # i.e. UninterpretedSort
        if il.is_first_order_sort(sort):
            decl = pyv.SortDecl(sort.name)
            self.sorts.append(decl)
        elif il.is_enumerated_sort(sort):
            # Declare the sort
            decl = pyv.SortDecl(sort.name)
            pyv_sort = Translation.to_pyv_sort(sort)
            self.sorts.append(decl)

            # Add constants (individuals) for each enum value
            # For some reason, not all enum variants show up in sig.symbols,
            # so we cannot add them in `translate_ivy_sig`
            for enum_value in sort.defines():
                const = pyv.ConstantDecl(enum_value, pyv_sort, False)
                self.constants.append(const)

            # Add distinct axioms
            individuals = [pyv.Id(name) for name in sort.defines()]
            op = pyv.NaryExpr("DISTINCT", tuple(individuals))
            axiom = pyv.AxiomDecl("{}_distinct".format(sort.name), op)
            self.axioms.append(axiom)
        elif il.is_boolean_sort(sort):
            # No need to declare the bool sort
            pass
        else:
            # print("unhandled sort: {}".format(sort))
            raise NotImplementedError("sort {} not supported".format(sort))

    def translate_ivy_sig(self, sig: il.Sig):
        '''Translate a module signature to the sorts, constants,
        relations, and functions of a mypyvy specification.
        To correctly infer which symbols are immutable, this
        must be called AFTER `add_axioms_and_props`.
        '''
        # Add sorts
        for (_sort_name, sort) in sig.sorts.items():
            self.add_sort(sort)

        # # Add symbols, replacing "." with DOT_REPLACEMENT
        for _sym_name, sym in sig.symbols.items():
            assert _sym_name == sym.name, "symbol name mismatch: {} != {}".format(_sym_name, sym.name)
            sort = sym.sort
            kind = Translation.sort_type(sort)
            name = Translation.to_pyv_name(sym.name)

            # FIXME: how to determine if (im)mutable?
            # Ivy has no such distinction.
            is_mutable = (sym.name not in self.immutable_symbols)

            if kind == 'individual':
                pyv_sort = Translation.to_pyv_sort(sort)
                const = pyv.ConstantDecl(name, pyv_sort, is_mutable)
                self.add_constant_if_not_exists(const)
            elif kind == 'relation':
                assert sym.is_relation()
                pyv_sort = Translation.to_pyv_sort(sort)
                # assert isinstance(pyv_sort, tuple)
                rel = pyv.RelationDecl(name, pyv_sort, is_mutable)
                self.relations.append(rel)
            elif kind == 'function':
                (dom_sort, rng_sort) = Translation.to_pyv_sort(sort)
                fn = pyv.FunctionDecl(name, dom_sort, rng_sort, is_mutable)
                self.functions.append(fn)
 
    def add_axioms_and_props(self, mod: im.Module):
        '''Add axioms and properties to the mypyvy program.'''
        # Add axioms
        # For some reason, these are directly formulas, rather than AST nodes
        for ax in mod.axioms:
            # ...and therefore don't have axiom names
            fmla = Translation.translate_logic_fmla(ax)
            axiom = pyv.AxiomDecl(None, fmla)
            self.axioms.append(axiom)
            # Mark symbols as immutable if they appear in axioms
            self.immutable_symbols |= Translation.globals_in_fmla(ax)

        # Add properties that are assumed to be true in this isolate
        for prop in mod.labeled_props:
            if prop.assumed:
                fmla = Translation.translate_logic_fmla(prop.formula)
                axiom = pyv.AxiomDecl(Translation.to_pyv_name(prop.label.relname), fmla)
                self.axioms.append(axiom)

    def add_conjectures(self, mod: im.Module):
        '''Add conjectures (claimed invariants) to the mypyvy program.'''
        # Add conjectures
        for conj in mod.labeled_conjs:
            fmla = Translation.translate_logic_fmla(conj.formula)
            inv = pyv.InvariantDecl(Translation.to_pyv_name(conj.label.relname), fmla, False, False)
            self.invariants.append(inv)

    def add_initializers(self, mod: im.Module):
        '''Add initializers to the mypyvy program.'''
        for (name, init) in mod.initializers:
            name = Translation.to_pyv_name(name)
            fmla = Translation.initializer_to_fmla(init)
            decl = pyv.InitDecl(name, fmla)
            self.initializers.append(decl)

    def add_public_actions(self, mod: im.Module):
        '''Add public actions to the mypyvy program.'''
        public_actions = filter(lambda x: x[0] in mod.public_actions, mod.actions.items())
        for (name, action) in public_actions:
            decl = Translation.translate_action(name, action)
            self.actions.append(decl)

    def to_program(self) -> pyv.Program:
        decls = self.sorts + self.constants + self.relations + self.functions \
            + self.axioms + self.initializers + self.actions + self.invariants
        return pyv.Program(decls)


def check_isolate():
    mod = im.module
    prog = MypyvyProgram()

    # FIXME: do we need to handle mod.aliases? (type aliases)

    # STEP 1: add axioms and conjectures
    # (and mark symbols as immutable if they appear in axioms)
    # mod.axioms
    # mod.labeled_props -> properties (become axioms once checked)
    # mod.labeled_conjs -> invariants/conjectures (to be checked)

    prog.add_axioms_and_props(mod)
    prog.add_conjectures(mod)

    # STEP 2: parse mod.sig to determine
    # sorts, relations, functions, and individuals
    # mod.sig.sorts & mod.sig.symbols
    prog.translate_ivy_sig(mod.sig)

    # STEP 3: generate actions
    # - collect all implicitly existentially quantified variables (those starting with __)
    # mod.initializers -> after init
    # mod.public_actions
    # mod.actions

    prog.add_initializers(mod)
    prog.add_public_actions(mod)

    #  Generate the program
    pyv_prog = prog.to_program()

    out_file = "{}.pyv".format(mod.name)
    with open(out_file, "w") as f:
        f.write(str(pyv_prog))
        print("output written to {}".format(out_file))

    exit(0)
