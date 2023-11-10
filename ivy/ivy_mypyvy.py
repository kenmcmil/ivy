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

# Our own class, which will be used to generate a mypyvy `Program`
class MypyvyProgram:
    # sort -> pyv.SortDecl
    # individual -> pyv.ConstantDecl (immutable)
    # axiom -> pyv.AxiomDecl

    def __init__(self):
        self.sorts = []
        self.constants = []
        self.axioms = []


    def add_sort(self, sort):
        # i.e. UninterpretedSort
        if il.is_first_order_sort(sort):
            decl = pyv.SortDecl(sort.name)
            self.sorts.append(decl)
        elif il.is_enumerated_sort(sort):
            # Declare the sort
            decl = pyv.SortDecl(sort.name)
            pyv_sort = pyv.UninterpretedSort(sort.name)
            self.sorts.append(decl)

            # FIXME: do we need this, or is it handled
            # when we add the symbols from the signature?
            # Add constants (individuals) for each enum value
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
            print("unhandled sort: {}".format(sort))
            pass
            # raise NotImplementedError("sort {} not supported".format(sort))

    def parse_ivy_sig(self, sig):
        # Add sorts
        for (sort_name, sort) in sig.sorts.items():
            self.add_sort(sort)

        # # Add symbols
        # for symbol in sig.symbols:
        #     if il.is_relation(symbol):
        #         pass
        #     elif il.is_function(symbol):
        #         pass
        #     elif il.is_constant(symbol):
        #         pass
        #     else:
        #         raise NotImplementedError("symbol {} not supported".format(symbol))

    def to_program(self):
        decls = self.sorts + self.constants + self.axioms
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

    # STEP 1: parse mod.sig to determine
    # sorts, relations, functions, and individuals
    prog.parse_ivy_sig(mod.sig)

    # Drop into a REPL by typing interact()
    import pdb;pdb.set_trace()

    out_file = "{}.pyv".format(mod.name)
    with open(out_file, "w") as f:
        pyv_prog = prog.to_program()
        f.write(str(pyv_prog))
        print("output written to {}".format(out_file))
        exit(0)