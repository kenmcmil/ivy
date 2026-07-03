# Regression tests for the files in this directory. See run_expects.py.
# These examples (model checking, liveness) can be slow, so raise the timeout.

defaults = {'timeout': 1000}

tests = [
    # ivy_check
    {'type': 'check', 'name': 'modular', 'expect': 'OK'},
    {'type': 'check', 'name': 'modular_mc', 'expect': 'OK'},
    {'type': 'check', 'name': 'liveness', 'expect': 'OK'},
    {'type': 'check', 'name': 'tactic', 'expect': 'OK'},
    {'type': 'check', 'name': 'leader_tutorial_without_proof',
     'args': ['isolate=abstract_model trace=true'],
     'expect': 'fail call abstract_model.elect'},
    {'type': 'check', 'name': 'leader_tutorial', 'expect': 'OK'},
    {'type': 'check', 'name': 'german_bmc_bug',
     'expect': 'BMC with bound 11 found a counter-example...'},
    {'type': 'check', 'name': 'german_mc_bug', 'expect': 'FAIL'},
    {'type': 'check', 'name': 'natural_deduction', 'expect': 'OK'},

    # repl and compilation via the ivyc (v2) compiler
    {'type': 'ivyc_repl', 'name': 'modular'},
    {'type': 'ivyc', 'name': 'borrow', 'expect': '', 'group': 'v2'},
]
