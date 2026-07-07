# Regression tests for the hardware examples. See run_expects.py.

# Well-formedness validation for an ivy_to_rtl result: yosys reads the emitted
# RTLIL (a structural sanity check). Used by the 'to_rtl' tests below.
_yosys_wf = 'yosys -q -p "read_rtlil {name}.il"'

tests = [
    # ---- ivy_check proofs ----

    # The pipelined-CPU reference-tagging proofs.
    {'type': 'check', 'name': 'pipe_cpu_ref', 'expect': 'OK', 'timeout': 300},
    {'type': 'check', 'name': '5stage_cpu_ref', 'expect': 'OK', 'timeout': 300},
    {'type': 'check', 'name': '5stage_bp_cpu_ref', 'expect': 'OK', 'timeout': 300},

    # A wire's post-state value must appear in a counterexample trace: the
    # invariant w ~= 5 fails when x reaches 4 (w = x+1 = 5), and the trace must
    # end with the post-state value w = 5.
    {'type': 'check', 'name': 'wiretrace', 'args': ['trace=true'],
     'expect': 'w = 5'},

    # These two memory-init probes are ivy_check targets too: memtest proves
    # out_val = 5, memtest2 proves out_val = out_val_alt.
    {'type': 'check', 'name': 'memtest', 'expect': 'OK'},
    {'type': 'check', 'name': 'memtest2', 'expect': 'OK'},

    # ---- ivy_to_rtl translation (group 'rtl') ----
    # Validation uses yosys, which is not installed in the default (nightly)
    # environment, so these are in group 'rtl'; run with group=rtl on a machine
    # that has yosys.

    {'type': 'to_rtl', 'name': 'test_to_rtl', 'validate': _yosys_wf, 'group': 'rtl'},
    {'type': 'to_rtl', 'name': 'refinement3', 'validate': _yosys_wf, 'group': 'rtl'},
    {'type': 'to_rtl', 'name': 'bfe_concat', 'validate': _yosys_wf, 'group': 'rtl'},
    {'type': 'to_rtl', 'name': 'pipe_cpu', 'validate': _yosys_wf, 'group': 'rtl'},
    {'type': 'to_rtl', 'name': 'pipe_cpu_ref', 'validate': _yosys_wf, 'group': 'rtl'},
    {'type': 'to_rtl', 'name': '5stage_cpu_ref', 'validate': _yosys_wf, 'group': 'rtl'},
    {'type': 'to_rtl', 'name': '5stage_bp_cpu_ref', 'validate': _yosys_wf, 'group': 'rtl'},

    # memtest: mem is initialized from a *defined* function init_mem(A)=5, so
    # the translation must emit a $meminit of 5 (DATA = repeated 0x05).
    {'type': 'to_rtl', 'name': 'memtest',
     'validate': _yosys_wf + ' && grep -q 0000010100000101 {name}.il',
     'group': 'rtl'},

    # memtest2: mem is initialized from an *undefined* symbol that is observed
    # elsewhere, which cannot be dropped soundly, so translation must error.
    {'type': 'to_rtl', 'name': 'memtest2',
     'expect': 'cannot translate initialization of array', 'group': 'rtl'},

    # arrcopy: a whole-array copy memb(A) := mema(A) in the update logic is not
    # a single-address RAM write, so translation must error.
    {'type': 'to_rtl', 'name': 'arrcopy',
     'expect': 'not a point write', 'group': 'rtl'},
]
