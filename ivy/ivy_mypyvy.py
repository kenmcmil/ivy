#
# Copyright (c) Microsoft Corporation. All Rights Reserved.
#

from . import ivy_module as im
from . import ivy_isolate
from . import ivy_compiler
from . import mypyvy_syntax as pyv

logfile = None
verbose = False

# We want to generate a mypyvy `Program` (in `mypyvy_syntax.py`)
def check_isolate():
    mod = im.module

    # Drop into a REPL by typing interact()
    import pdb;pdb.set_trace()

    # mod.sort_order
    # mod.isolates

    # with open("ivy.pyv", "w") as f:
    #     pass
    print("output written to ivy.pyv")
    exit(0)