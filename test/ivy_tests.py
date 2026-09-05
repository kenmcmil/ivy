# Regression tests for the files in this directory. See run_expects.py.

tests = [
    {'type': 'check', 'name': 'fba', 'expect': 'OK'},
    {'type': 'check', 'name': 'interpdef1',
     'expect': 'interpdef1.ivy: line 5: error: definition of interpreted symbol <'},
    {'type': 'check', 'name': 'whileexists1', 'expect': 'OK'},
    {'type': 'check', 'name': 'whilesome1', 'expect': 'OK'},
    {'type': 'check', 'name': 'whilesome2', 'expect': 'OK'},
    {'type': 'check', 'name': 'fundef1',
     'expect': 'error: Variable Y:t occurs free on right-hand side of definition'},
    {'type': 'check', 'name': 'fundef2',
     'expect': 'error: Variable X:t occurs twice on left-hand side of definition'},
    {'type': 'check', 'name': 'strat1',
     'expect': 'error: The verification condition is not in'},
    {'type': 'check', 'name': 'skolem1', 'expect': 'error: failed checks: 1'},
    {'type': 'check', 'name': 'ifstar1', 'expect': 'OK'},
    {'type': 'check', 'name': 'frag1', 'expect': 'OK'},
    {'type': 'check', 'name': 'frag2',
     'expect': 'An interpreted symbol is applied to a universally quantified variable'},
    {'type': 'check', 'name': 'frag3', 'expect': 'OK'},
    {'type': 'check', 'name': 'frag4',
     'expect': 'An interpreted symbol is applied to a universally quantified variable'},
    {'type': 'check', 'name': 'frag5', 'expect': 'OK'},
    {'type': 'check', 'name': 'frag6', 'expect': 'OK'},
    {'type': 'check', 'name': 'frag7',
     'expect': 'An interpreted symbol is applied to a universally quantified variable'},
    {'type': 'check', 'name': 'frag8',
     'expect': 'An interpreted symbol is applied to a universally quantified variable'},
    {'type': 'check', 'name': 'frag9',
     'expect': 'An interpreted symbol is applied to a universally quantified variable'},
    {'type': 'check', 'name': 'frag10',
     'expect': 'An interpreted symbol is applied to a universally quantified variable'},
    {'type': 'check', 'name': 'frag11', 'expect': 'OK'},
    {'type': 'check', 'name': 'frag12', 'expect': 'OK'},
    {'type': 'check', 'name': 'frag13', 'expect': 'OK'},
    {'type': 'check', 'name': 'frag14',
     'expect': 'An interpreted symbol is applied to a universally quantified variable'},
    {'type': 'check', 'name': 'frag15',
     'expect': 'An interpreted symbol is applied to a universally quantified variable'},
    {'type': 'check', 'name': 'frag16', 'expect': 'OK'},
    {'type': 'check', 'name': 'frag17', 'expect': 'OK'},
    {'type': 'check', 'name': 'frag18', 'expect': 'OK'},
    {'type': 'check', 'name': 'frag19', 'expect': 'OK'},
    {'type': 'check', 'name': 'oddeven', 'args': ['complete=fo'], 'expect': 'OK'},
    {'type': 'check', 'name': 'oddeven2', 'args': ['complete=fo'], 'expect': 'OK'},
    {'type': 'check', 'name': 'oddeven3', 'expect': 'OK'},
    {'type': 'check', 'name': 'oddeven4', 'expect': 'OK'},
    {'type': 'check', 'name': 'learning_switch1', 'args': ['trace=true'],
     'expect': 'learning_switch1.ivy: line 37:'},
    {'type': 'check', 'name': 'ded1', 'expect': 'OK'},

    # The `using` clause and `patdef` named patterns: fine-grained choice of the
    # inductive hypotheses used in a consecution check (doc/projects/
    # invariant_choice.md). usingpat1: `using` selects the needed hypothesis ->
    # OK. usingpat2: omitting it yields a (false) CTI. usingpat3: the |, -, and *
    # operators select hypothesis sets (two patterns drop a needed one -> 2
    # failures). usingpat4: patdef, chained and used with difference (one drops a
    # needed one -> 1 failure). usingpat5: `$` root-anchors a leaf. patdef1: a
    # duplicate patdef name is caught. patdef2/patdef3: object-scoped patdefs
    # with cross-object references, the latter through a module instance.
    {'type': 'check', 'name': 'usingpat1', 'expect': 'OK'},
    {'type': 'check', 'name': 'usingpat2', 'expect': 'error: failed checks: 1'},
    {'type': 'check', 'name': 'usingpat3', 'expect': 'error: failed checks: 2'},
    {'type': 'check', 'name': 'usingpat4', 'expect': 'error: failed checks: 1'},
    {'type': 'check', 'name': 'usingpat5', 'expect': 'OK'},
    {'type': 'check', 'name': 'patdef1', 'expect': 'error: redefining x'},
    {'type': 'check', 'name': 'patdef2', 'expect': 'OK'},
    {'type': 'check', 'name': 'patdef3', 'expect': 'OK'},
]
