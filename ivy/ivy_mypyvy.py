#
# Copyright (c) Microsoft Corporation. All Rights Reserved.
#

from . import ivy_ast as ia
from . import ivy_logic as il
from . import ivy_logic_utils as ilu
from . import ivy_module as im
from . import ivy_trace as it
from . import logic as lg
from . import mypyvy_syntax as pyv

logfile = None
verbose = False

# Ivy symbols have dots in them (due to the module system)
# but mypyvy doesn't allow dots in names, so we replace
# them with this string
DOT_REPLACEMENT = "_"

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
            return ivy_name.replace(".", DOT_REPLACEMENT)
        raise Exception("cannot translate non-string name {} to mypyvy ".format(repr(ivy_name)))

    def translate_logic_fmla(fmla) -> pyv.Expr:
        '''Translates a logic formula (as defined in logic.py) to a
        mypyvy expression. (Note: these for some reason are not AST nodes.)'''

        def translate_binders(binders) -> tuple[pyv.SortedVar]:
            vars = []
            for binder in binders:
                name = Translation.to_pyv_name(binder.name)
                sort = Translation.to_pyv_sort(binder.sort)
                vars.append(pyv.SortedVar(name, sort, None))
            return vars

        if isinstance(fmla, lg.ForAll):
            # fmla.variables & fmla.body
            return pyv.Forall(translate_binders(fmla.variables), Translation.translate_logic_fmla(fmla.body))
        elif isinstance(fmla, lg.Exists):
            # fmla.variables & fmla.body
            return pyv.Exists(translate_binders(fmla.variables), Translation.translate_logic_fmla(fmla.body))
        elif isinstance(fmla, lg.Ite):
            # fmla.sort & fmla.cond & fmla.t_then, fmla.t_else
            return pyv.IfThenElse(Translation.translate_logic_fmla(fmla.cond), Translation.translate_logic_fmla(fmla.t_then), Translation.translate_logic_fmla(fmla.t_else))
        elif isinstance(fmla, lg.And):
            # fmla.terms
            return pyv.And(*tuple([Translation.translate_logic_fmla(x) for x in fmla.terms]))
        elif isinstance(fmla, lg.Or):
            # fmla.terms
            return pyv.Or(*tuple([Translation.translate_logic_fmla(x) for x in fmla.terms]))
        elif isinstance(fmla, lg.Eq):
            # fmla.t1 & fmla.t2
            return pyv.Eq(Translation.translate_logic_fmla(fmla.t1), Translation.translate_logic_fmla(fmla.t2))
        elif isinstance(fmla, lg.Implies):
            # fmla.t1 & fmla.t2
            return pyv.Implies(Translation.translate_logic_fmla(fmla.t1), Translation.translate_logic_fmla(fmla.t2))
        elif isinstance(fmla, lg.Iff):
            # fmla.t1 & fmla.t2
            return pyv.Iff(Translation.translate_logic_fmla(fmla.t1), Translation.translate_logic_fmla(fmla.t2))
        elif isinstance(fmla, lg.Not):
            # fmla.body
            return pyv.Not(Translation.translate_logic_fmla(fmla.body))
        elif isinstance(fmla, lg.Apply):
            # FIXME: this doesn't work for relations
            # fmla.func & fmla.terms
            return pyv.Apply(Translation.to_pyv_name(fmla.func.name), tuple([Translation.translate_logic_fmla(x) for x in fmla.terms]))
        elif isinstance(fmla, lg.Const) or isinstance(fmla, lg.Var):
            return pyv.Id(Translation.to_pyv_name(fmla.name))
        else:
            raise NotImplementedError("translating logic formula {} to mypyvy ".format(repr(fmla)))


# Our own class, which will be used to generate a mypyvy `Program`
class MypyvyProgram:
    # sort -> pyv.SortDecl
    # individual -> pyv.ConstantDecl (immutable)
    # axiom -> pyv.AxiomDecl

    def __init__(self):
        self.sorts = []
        self.constants = []
        self.relations = []
        self.functions = []
        self.axioms = []
        self.invariants = []

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
        relations, and functions of a mypyvy specification.'''
        # Add sorts
        for (sort_name, sort) in sig.sorts.items():
            self.add_sort(sort)

        # # Add symbols, replacing "." with DOT_REPLACEMENT
        for _sym_name, sym in sig.symbols.items():
            assert _sym_name == sym.name, "symbol name mismatch: {} != {}".format(_sym_name, sym.name)
            sort = sym.sort
            kind = Translation.sort_type(sort)
            name = Translation.to_pyv_name(sym.name)

            # FIXME: how to determine if (im)mutable?
            # Ivy has no such distinction.
            is_mutable = True

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
            inv = pyv.AxiomDecl(Translation.to_pyv_name(conj.label.relname), fmla)
            self.invariants.append(inv)

    def to_program(self) -> pyv.Program:
        decls = self.sorts + self.constants + self.relations + self.functions + self.axioms
        return pyv.Program(decls)


def check_isolate():
    mod = im.module
    prog = MypyvyProgram()

    # FIXME: do we need to handle mod.aliases? (type aliases)

    # STEP 1: parse mod.sig to determine
    # sorts, relations, functions, and individuals
    # mod.sig = sig
    #   sig.sorts
    #   sig.symbols (and sig.all_symbols())
    prog.translate_ivy_sig(mod.sig)

    # STEP 2: add axioms and conjectures
    # Drop into a REPL by typing interact()
    # mod.axioms
    # mod.labeled_props -> properties (become axioms once checked)
    # mod.labeled_conjs -> invariants/conjectures (to be checked)

    import pdb;pdb.set_trace()

    prog.add_axioms_and_props(mod)
    prog.add_conjectures(mod)

    # STEP 3: generate actions
    # - collect all implicitly existentially quantified variables (those starting with __)
    # mod.initializers -> after init
    # mod.public_actions
    # mod.actions

    # Generate VCs:
    # _true = lg.And()
    # _false = lg.Or()
    # it.make_vc(action, _true, _false)

    # What's used in ivy_vmt.py seems easier to work with
    # upd = a.update(im.module,None)
    # upd[0] describes the referenced symbols? (or modified symbols?)
    # upd[1] describes the formula

    #  Generate the program
    pyv_prog = prog.to_program()

    out_file = "{}.pyv".format(mod.name)
    with open(out_file, "w") as f:
        f.write(str(pyv_prog))
        print("output written to {}".format(out_file))

    exit(0)
