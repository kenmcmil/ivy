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
    # The SPECULATING 5-stage pipeline (decomp.md "Speculation pattern"): the
    # control-hazard stall on the pc is replaced by speculation. _spec makes the
    # fixed "not taken" guess (flush + squash on a taken branch); _bp adds a real
    # branch predictor as an isolate with no interface spec, so the proof holds
    # for any prediction.
    {'type': 'check', 'name': '5stage_spec_cpu_dec', 'expect': 'OK', 'timeout': 300},
    {'type': 'check', 'name': '5stage_bp_cpu_dec', 'expect': 'OK', 'timeout': 300},

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

    # The speculating pipelines. The proof says nothing about prediction quality
    # (correctness holds for ANY prediction), so simulation is the only check on
    # the predictor's behavior -- see the note at the end of decomp.md's
    # "Adding a branch predictor". prog.hex loops on an always-taken BEQZ, so the
    # pc traces distinguish the two: _spec fetches past the branch (4 -> 5) and
    # redirects EVERY iteration (always-mispredict signature), while _bp does so
    # once and then, after the 2-bit counter saturates, predicts correctly with
    # no further wrong-path fetches (learning signature).
    {'type': 'to_rtl', 'name': '5stage_spec_cpu_dec',
     'validate': _yosys_wf
                 + ' && ./sim_cpu_dec.sh {name} prog.hex 30'
                 + ' | grep -q "4 -> 5 -> 2 -> 3 -> 4 -> 5 -> 2"',
     'group': 'rtl'},
    {'type': 'to_rtl', 'name': '5stage_bp_cpu_dec',
     'validate': _yosys_wf
                 + ' && ./sim_cpu_dec.sh {name} prog.hex 30'
                 + ' | grep -q "4 -> 5 -> 2 -> 3 -> 2 -> 3"',
     'group': 'rtl'},

    # The cache stage-decomposition CPU (5stage_cache_cpu_dec): I-cache, write-
    # back D-cache, and FLUSH-based fetch coherence, exercised on the GENERATED
    # RTL. sim_cache_cpu_dec.sh injects each program into the UNIFIED \mem (both
    # caches sit in front of it), runs yosys sim, and reports the pc trace, the
    # committed register writes (WB:), and per-cache stall-cycle counts. The
    # proof already shows correctness for every program; these sims check the
    # caches are FUNCTIONAL and deliver the intended SPEEDUP (cold-miss stalls
    # only). Larger design -> 600s timeout, like the cache reference model.

    # (1) I-cache: a 6-instruction infinite loop over 3 cache lines. The cold
    # first pass stalls every fetch (IFETCH_STALL_CYCLES counts only those); once
    # the lines are cached the warm loop runs at one instruction per cycle with
    # NO further fetch stalls -- the pc trace shows 0..5 cycling unbroken, and the
    # total stall count stays at the cold-miss floor (7). No data accesses (0).
    {'type': 'to_rtl', 'name': '5stage_cache_cpu_dec',
     'validate': _yosys_wf
                 + ' && ./sim_cache_cpu_dec.sh {name} icache_prog.hex 46 > {name}.simout 2>&1'
                 + ' && grep -q "0 -> 1 -> 2 -> 3 -> 4 -> 5 -> 0 -> 1 -> 2 -> 3 -> 4 -> 5" {name}.simout'
                 + ' && grep -q "IFETCH_STALL_CYCLES: 7" {name}.simout'
                 + ' && grep -q "DMEM_STALL_CYCLES: 0" {name}.simout',
     'timeout': 600, 'group': 'rtl'},

    # (2) D-cache: ST [64]; ST [65]; LD [64]; LD [65] -- all one two-word line.
    # FUNCTIONAL: both loads return the stored value (WB shows r3=42 r4=42).
    # SPEEDUP: exactly ONE cold miss (DMEM_STALL_CYCLES: 4, the write-allocate
    # fill on the first store); the second store and both loads are warm hits
    # that add no stall -- one fill amortized across a store and two loads.
    {'type': 'to_rtl', 'name': '5stage_cache_cpu_dec',
     'validate': _yosys_wf
                 + ' && ./sim_cache_cpu_dec.sh {name} dcache_prog.hex 46 > {name}.simout 2>&1'
                 + ' && grep -q "WB: r1=64 r2=42 r5=65 r3=42 r4=42" {name}.simout'
                 + ' && grep -q "DMEM_STALL_CYCLES: 4" {name}.simout',
     'timeout': 600, 'group': 'rtl'},

    # (3) self-modifying code via FLUSH: LD a new instruction word (0xC00E =
    # BEQZ r0,14 = 49166), ST it over the instruction at address 8 (originally
    # BEQZ r0,12), FLUSH [8], then jump to 8. WB shows the new word was loaded
    # (r3=49166); the pc branches to the NEW target 14 (settling in 14 -> 15 ->
    # 14), NOT the old 12 -- the store+FLUSH made the modified instruction
    # visible to fetch (write-back to \mem + I-cache eviction). Without the FLUSH
    # this would be an ISA fetch-coherence error.
    {'type': 'to_rtl', 'name': '5stage_cache_cpu_dec',
     'validate': _yosys_wf
                 + ' && ./sim_cache_cpu_dec.sh {name} smc_prog.hex 46 > {name}.simout 2>&1'
                 + ' && grep -q "WB: r1=8 r2=16 r3=49166" {name}.simout'
                 + ' && grep -q "14 -> 15 -> 14" {name}.simout',
     'timeout': 600, 'group': 'rtl'},

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
