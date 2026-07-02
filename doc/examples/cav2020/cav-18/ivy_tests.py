# Regression tests for the files in this directory. See run_expects.py.

defaults = {'timeout': 1000}

tests = [
    {'type': 'check', 'name': 'german_inv', 'expect': 'OK'},
    {'type': 'check', 'name': 'flash_inv', 'expect': 'OK'},
    {'type': 'check', 'name': 'tomasulo_inv', 'expect': 'OK'},
    {'type': 'check', 'name': 'vs_paxos_inv', 'expect': 'OK'},
    {'type': 'check', 'name': 'german_mc', 'expect': 'OK'},
    {'type': 'check', 'name': 'flash_mc', 'expect': 'OK'},
    {'type': 'check', 'name': 'tomasulo_mc', 'expect': 'OK'},
    {'type': 'check', 'name': 'vs_paxos_mc', 'expect': 'OK'},
]
