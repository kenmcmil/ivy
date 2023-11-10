#
# Copyright (c) Microsoft Corporation. All Rights Reserved.
#

from . import ivy_module as im
from . import ivy_logic as il
from . import ivy_isolate
from . import ivy_compiler
from . import mypyvy_syntax as pyv

logfile = None
verbose = False

# Ivy symbols have dots in them (due to the module system)
# but mypyvy doesn't allow dots in names, so we replace
# them with this string
DOT_REPLACEMENT = "__"

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

    def sort_type(self, ivy_sort):
        if il.is_function_sort(ivy_sort) and il.is_boolean_sort(ivy_sort.rng):
            return 'relation'
        elif il.is_function_sort(ivy_sort):
            return 'function'
        return 'individual'

    def to_pyv_sort(self, ivy_sort):
        if il.is_first_order_sort(ivy_sort) \
            or il.is_enumerated_sort(ivy_sort):
            return pyv.UninterpretedSort(ivy_sort.name)
        elif il.is_boolean_sort(ivy_sort):
            return pyv.BoolSort
        # Relation
        elif il.is_function_sort(ivy_sort) and il.is_boolean_sort(ivy_sort.rng):
            # FIXME: do we need the bool for rng?
            return tuple([self.to_pyv_sort(x) for x in ivy_sort.dom])
        elif il.is_function_sort(ivy_sort):
            return (tuple([self.to_pyv_sort(x) for x in ivy_sort.dom]), self.to_pyv_sort(ivy_sort.rng))
        else:
            raise NotImplementedError("translating sort {} to mypyvy ".format(repr(ivy_sort)))

    def to_pyv_name(self, ivy_name):
        return ivy_name.replace(".", DOT_REPLACEMENT)


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
            pyv_sort = self.to_pyv_sort(sort)
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

    def translate_ivy_sig(self, sig):
        # Add sorts
        for (sort_name, sort) in sig.sorts.items():
            self.add_sort(sort)

        # # Add symbols, replacing "." with DOT_REPLACEMENT
        for _sym_name, sym in sig.symbols.items():
            assert _sym_name == sym.name, "symbol name mismatch: {} != {}".format(_sym_name, sym.name)
            sort = sym.sort
            kind = self.sort_type(sort)
            name = self.to_pyv_name(sym.name)

            # FIXME: how to determine if (im)mutable?
            # Ivy has no such distinction.
            is_mutable = True

            if kind == 'individual':
                pyv_sort = self.to_pyv_sort(sort)
                const = pyv.ConstantDecl(name, pyv_sort, is_mutable)
                self.add_constant_if_not_exists(const)
            elif kind == 'relation':
                assert sym.is_relation()
                pyv_sort = self.to_pyv_sort(sort)
                # assert isinstance(pyv_sort, tuple)
                rel = pyv.RelationDecl(name, pyv_sort, is_mutable)
                self.relations.append(rel)
            elif kind == 'function':
                (dom_sort, rng_sort) = self.to_pyv_sort(sort)
                fn = pyv.FunctionDecl(name, dom_sort, rng_sort, is_mutable)
                self.functions.append(fn)

    def to_program(self):
        decls = self.sorts + self.constants + self.relations + self.functions + self.axioms
        return pyv.Program(decls)


def check_isolate():
    mod = im.module
    prog = MypyvyProgram()

    # mod.sort_order -> sorts
    # mod.functions -> all relations, constants, and functions?
    # mod.labeled_props -> properties/conjectures/invariants
    # mod.initializers -> after init
    # mod.public_actions
    # mod.actions
    # mode.sig = sig
    #   sig.sorts
    #   sig.symbols (and sig.all_symbols())
    #   sig.constructors
    #   sig.interp
    # take a look at sig_to_str()
    # mod.isolates

    # Drop into a REPL by typing interact()
    import pdb;pdb.set_trace()

    # STEP 1: parse mod.sig to determine
    # sorts, relations, functions, and individuals
    prog.translate_ivy_sig(mod.sig)

    #  Generate the program
    pyv_prog = prog.to_program()

    out_file = "{}.pyv".format(mod.name)
    with open(out_file, "w") as f:
        f.write(str(pyv_prog))
        print("output written to {}".format(out_file))

    exit(0)
