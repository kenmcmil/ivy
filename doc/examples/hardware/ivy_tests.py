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
    # The stage-DECOMPOSITION 5-stage pipeline: each stage and each inter-stage
    # interface is its own isolate, with `register` pipe outputs and ghost
    # interface isolates (see doc/projects/decomposition.md).
    {'type': 'check', 'name': '5stage_cpu_dec', 'expect': 'OK', 'timeout': 300},

    # The small stage-decomposition tutorial pipelines (doc/examples/hardware/
    # decomp.md): a 3-stage simple read-after-write hazard, and three complex
    # (early/late write) hazard variants -- unconditional, decode-time
    # conditional, and register-dependent (late-resolved) conditional writes.
    {'type': 'check', 'name': 'simple3_dec', 'expect': 'OK'},
    {'type': 'check', 'name': 'complex3_dec', 'expect': 'OK'},
    {'type': 'check', 'name': 'complex3_cload_dec', 'expect': 'OK'},
    {'type': 'check', 'name': 'complex3_cmax_dec', 'expect': 'OK'},

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
    # The ivy1.8 sugar `a<<i:j>>` (bfe) and `a::b` (concat) must desugar to the
    # same design as the explicit bfe_concat.ivy: validate that the two emitted
    # netlists have the same set of lines (ignoring the generated-from-source
    # comment; sorted, since ivy_to_rtl's wire/connect emission order is not
    # stable across separate runs).
    {'type': 'to_rtl', 'name': 'bfe_concat_sugar',
     'validate': _yosys_wf + ' && ivy_to_rtl bfe_concat.ivy'
                 + ' && diff <(grep -v "^# Generated" {name}.il | sort)'
                 + ' <(grep -v "^# Generated" bfe_concat.il | sort)',
     'group': 'rtl'},
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

    # The stage-decomposition CPU exercises cross-isolate `register` reads
    # (pipe registers consumed by the next stage / decoded in the parent) and a
    # separate imem/mem, so validation goes beyond a yosys read: it simulates
    # prog.hex end to end via sim_cpu_dec.sh (inject the program into \imem,
    # flatten the per-stage modules, run yosys sim) and checks the pc trace shows
    # the pipeline filling (0..4) and the BEQZ redirecting back to 2.
    {'type': 'to_rtl', 'name': '5stage_cpu_dec',
     'validate': _yosys_wf
                 + ' && ./sim_cpu_dec.sh {name} prog.hex 20'
                 + ' | grep -q "0 -> 1 -> 2 -> 3 -> 4 -> 2 -> 3"',
     'group': 'rtl'},

    # The input-driven CMAX pipeline (decomp.md's register-dependent complex
    # hazard). It has no instruction memory -- instructions arrive on the primary
    # input inst_in -- and its late write uses the `<` operator, so this exercises
    # the ivy_to_rtl relational-operator support. Validation simulates cmax_prog
    # via sim_cpu_input.sh (a feedback harness whose pointer advances only when
    # ~issue_stall) and checks the r trace (INC early writes, CMAX 5 rounds 1->5,
    # CMAX 4 does not write) and that a stall actually occurred.
    {'type': 'to_rtl', 'name': 'complex3_cmax_dec',
     'validate': _yosys_wf
                 + ' && ./sim_cpu_input.sh {name} cmax_prog.hex 16 issue_stall r'
                 + ' > {name}.simout'
                 + ' && grep -q "0 -> 1 -> 5 -> 6 -> 7" {name}.simout'
                 + ' && grep -q "stalls observed: yes" {name}.simout',
     'group': 'rtl'},

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
