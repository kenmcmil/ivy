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
    # The cache CPU: I/D caches, FLUSH, and a multi-cycle memory (see
    # add_cache_to_cpu.md). Larger, so a longer timeout.
    {'type': 'check', 'name': '5stage_cache_cpu_ref', 'expect': 'OK', 'timeout': 600},

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
    # For the cache CPU, validation goes further than a yosys read: it proves,
    # by inductive combinational equivalence (equiv_induct), that the emitted
    # RTL matches an independent hand-written SystemVerilog golden model
    # (cpu_golden.sv), register/memory by register/memory. See cpu_equiv.ys.
    {'type': 'to_rtl', 'name': '5stage_cache_cpu_ref',
     'validate': _yosys_wf + ' && yosys -q cpu_equiv.ys',
     'timeout': 600, 'group': 'rtl'},

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

    # Handling of functions defined by `definition` (see the ivy_to_rtl fix):
    # a wire function used by the implementation is inlined (no lookup memory),
    # a specification function is ignored, and an ordinary (non-wire) function
    # applied in the implementation is an error.
    {'type': 'to_rtl', 'name': 'to_rtl_wire_fun',
     'validate': _yosys_wf + ' && ! grep -q wfdbl {name}.il', 'group': 'rtl'},
    {'type': 'to_rtl', 'name': 'to_rtl_spec_fun',
     'validate': _yosys_wf + ' && ! grep -q sfq {name}.il', 'group': 'rtl'},
    {'type': 'to_rtl', 'name': 'to_rtl_bad_fun',
     'expect': 'non-wire function', 'group': 'rtl'},
]
