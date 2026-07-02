# Regression tests for the files in this directory. See run_expects.py.

defaults = {'timeout': 1000}

tests = [
    {'type': 'check', 'name': 'ticket', 'expect': 'OK'},
    {'type': 'check', 'name': 'ticket_nested', 'expect': 'OK'},
]
