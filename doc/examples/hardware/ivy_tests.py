# Regression tests for the hardware examples. See run_expects.py.
#
# The other files in this directory (test_to_rtl, refinement*, bfe_concat,
# pipe_cpu) are ivy_to_rtl translation examples rather than ivy_check targets,
# so they are not listed here.

tests = [
    # The pipelined-CPU reference-tagging proofs.
    {'type': 'check', 'name': 'pipe_cpu_ref', 'expect': 'OK', 'timeout': 300},
    {'type': 'check', 'name': '5stage_cpu_ref', 'expect': 'OK', 'timeout': 300},

    # A wire's post-state value must appear in a counterexample trace: the
    # invariant w ~= 5 fails when x reaches 4 (w = x+1 = 5), and the trace must
    # end with the post-state value w = 5.
    {'type': 'check', 'name': 'wiretrace', 'args': ['trace=true'],
     'expect': 'w = 5'},
]
