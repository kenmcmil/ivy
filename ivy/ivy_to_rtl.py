#! /usr/bin/env python
#
# Copyright (c) Microsoft Corporation. All Rights Reserved.
#

from . import ivy_init
from . import ivy_logic as il
from . import ivy_module as im
from . import ivy_utils as iu
from . import ivy_actions as ia
from . import logic as lg
from . import logic_util as lu
from . import ivy_solver as slv
from . import ivy_transrel as tr
from . import ivy_logic_utils as ilu
from . import ivy_compiler as ic
from . import ivy_isolate as iso
from . import ivy_ast
import itertools
from . import ivy_cpp
from . import ivy_cpp_types
from . import ivy_fragment as ifc
from . import ivy_printer
import sys
import os
import platform

from collections import defaultdict
from operator import mul
import re
from functools import reduce




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

        mod_name = im.module.name  # root name for the output file
        with iu.ErrorPrinter():
            ivy_printer.print_module(im.module)

        # TODO: add code here to emit the module in RTLIL format
            

if __name__ == "__main__":
    main_int(True)
        
