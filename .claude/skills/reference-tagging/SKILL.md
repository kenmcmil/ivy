---
name: reference-tagging
description: >-
  Specify and verify a pipelined hardware microarchitecture against an ISA
  reference in Ivy (ivy1.8) using the "reference tagging" method: a ghost trace
  of ISA states, a tag per pipeline element pointing into the trace, and a small
  local invariant per element. Use when modeling or proving an in-order CPU
  pipeline correct against its instruction set -- including data-hazard stalls,
  control hazards, and branch speculation -- and when preparing such a model for
  ivy_to_rtl translation. Not needed for non-hardware Ivy work.
---

# Reference tagging for pipeline verification

Reference tagging verifies a hardware pipeline against an *executable ISA
reference* instead of a hand-written monolithic invariant. You keep, as ghost
state, a **trace**: the sequence of architectural states the ISA passes through,
one entry per instruction. The hardware has many instructions in flight; you tag
each microarchitectural element with a **trace index** naming the instruction it
is working on, then prove, per element, that its contents equal the trace value
*at its tag*. This decomposes the proof into one simple invariant per pipeline
latch / register file / memory, and the *same trace model is reused unchanged*
as the microarchitecture grows.

`references/` contains four worked, fully-verified examples that this skill is
distilled from — read the one closest to your target before writing code:

- `pipe_cpu_ref.ivy` — 2-stage pipeline (the tutorial base case).
- `5stage_cpu_ref.ivy` — standard 5-stage (IF/ID/EX/MEM/WB) with data-hazard
  stalls and non-speculative branches.
- `5stage_bp_cpu_ref.ivy` — 5-stage with a speculative branch predictor (shadow
  bits).
- `5stage_cache_cpu_ref.ivy` — adds I/D caches, a `FLUSH` instruction, and a
  multi-cycle memory; the reference is extended with `ddirty`/`error` to model
  cache incoherence (see "Caches, incoherence, multi-cycle memory" below).
- `reference_tagging.md` — the prose writeup of the method.

## The three ingredients

1. **ISA model** (`module isa_model(init_mem, init_imem)`): the architectural
   state (`pc`, `rf`, `mem`, `imem`) as `var`s, the per-instruction
   intermediate values as **defined functions**, and one `action step` that
   executes a single instruction.

2. **`trace` isolate**: instantiates the ISA as `arch` and an abstract sequence
   type `tag`; stores an array `st(T:tag) : state_t` of recorded states and a
   pointer `now : tag`. Provides ghost `action step` (advance `arch`, extend the
   trace). Carries the auxiliary invariants that make the recorded history a
   faithful ISA execution.

3. **The implementation** (`object cpu`): the real datapath, plus ghost `tag`
   variables for each stage and local invariants relating each stage's contents
   to `trace.st(<its tag>)`. Ghost updates live in a `specification { ... }`
   block, never in the datapath.

## Recipe

1. **Types and I/O.** Declare bit-vector types (`type word; interpret word ->
   bv[16]`, etc.). The clock is `export action posedge`. Initial memory contents
   are top-level *uninterpreted* functions `init_mem`, `init_imem` (arbitrary
   fixed image), passed to `isa_model`; the cpu initializes its own memories
   from the same functions, so the proof holds for any program. (See "Memory
   init" below for why this must be shared and uninterpreted.)

2. **Write `isa_model`.** State as `var`s. Intermediate values as `function`s
   (`function opcode = bfe[13][15](fetched) : opc`, `function a_val = rf(ra) :
   word`, `function take_branch = (opcode=6)&(a_val=0) : bool`, ...). `after
   init` sets `pc`, zeroes `rf`, and loads `mem(A) := init_mem(A)`,
   `imem(A) := init_imem(A)`. `action step` / `after step` executes one
   instruction and updates the PC using `old take_branch` (see gotchas).

3. **Write the `trace` isolate.** `instance arch : isa_model(init_mem,
   init_imem)`; `instance tag : unbounded_sequence`; a `state_t` struct with the
   architectural state *and every intermediate value*; `var now`, `var st`; an
   `action current` that snapshots `arch` into a `state_t`; `action step = {
   arch.step; now := now.next; st(now) := current }`; `after init { now := 0;
   st(now) := current }`. Close the isolate with `with addr,opc` (see gotchas).

4. **Trace auxiliary invariants** (boilerplate — mirror the ISA transition over
   recorded entries; an LLM can generate these from `isa_model`):
   - `st(now).X = arch.X` for every field X.
   - Consistency for *all* recorded entries: `T <= now -> st(T).opcode =
     bfe[13][15](st(T).fetched)`, `... st(T).a_val = st(T).rf(st(T).ra)`, etc.
   - Step relation between consecutive entries: `succ(T,U) & U <= now ->
     st(U).pc = (st(T).target if st(T).take_branch else st(T).pc + 1)`, and
     likewise for `rf`, `mem`, `imem`. Without these, past entries `st(T)` for
     `T<now` are unconstrained and the cpu proof fails.

5. **Implementation datapath.** Model combinational signals as `wire` +
   `definition`, registers/latches as `var`, memories as `var f(A:addr):word`.
   Each stage decodes its instruction word with `bfe`; stalls/squashes are
   ordinary `if`s over the latches.

6. **Ghost tags + step in the `specification` block.** Give each stage a
   `var <stage>_tag : trace.tag` (or boundary counters `commit/mcommit/...`, one
   per stage boundary, for deeper pipes). In a **ghost `after posedge` inside
   `specification`**, advance the tags mirroring the datapath's stage movement
   and call `trace.step` exactly when a valid instruction is issued on the
   correct path. A tag does *not* advance when its stage stalls or is squashed.

7. **Per-stage invariants.** For each stage: `<valid> -> <ir> =
   trace.st(<tag>).fetched`; `rf(R) = trace.st(<commit tag>).rf(R)`; `mem(M) =
   trace.st(<mem tag>).mem(M)`; and, for computed latch values, tie them to the
   trace's recorded intermediate values (e.g. `m_valid & m_opcode=1 -> m_res =
   st(mcommit).a_val + st(mcommit).b_val`). Also the structural tag invariants
   (the pipeline occupancy is a contiguous run of trace indices) and a PC
   invariant (`~fetch_stall -> pc = st(now).pc`, plus the fall-through case
   while a branch is pending).

8. **Verify:** `ivy_check <file>.ivy` should print `OK`. Iterate on
   counterexamples (`ivy_check trace=true ...`; write per-CTI failures to files
   with `trace_dir=<dir>`). Missing invariants usually show up as spurious
   (unreachable) pre-states — add the structural fact that rules them out.

## Gotchas (each cost real debugging time)

- **Abstract models use defined functions, not wires; use `old`.** A `wire` is
  frozen at its pre-clock value for the whole action, which is wrong for the
  ISA, where intermediate values must track the state as `step` mutates it. Use
  `function` (re-evaluated on each state change). Consequently a defined
  function can change *mid-action*: to read its start-of-action value (e.g. the
  branch decision before the writeback), use `old` — the PC update must be
  `if old take_branch { ... }`. Getting this wrong makes `take_branch` read the
  post-writeback value and breaks the proof.

- **`bfe` result sort must be pinned.** `bfe[i][j]` is fully polymorphic in its
  result; when compared to a numeric literal, ascribe it: `(bfe[13][15](x):opc)
  = 6`. When it defines a value of known sort (`wire opcode : opc; definition
  opcode = bfe[13][15](ir)`) the sort is inferred.

- **Interpret the small bit-vector types in the trace isolate.** Quantified
  invariants that compare recorded fields to numerals need the bit-vector
  interpretation, or the solver collapses distinct numerals. Close the trace
  isolate with `with addr,opc` (interpreting `word` is not needed for these).

- **Memory init must be shared and uninterpreted.** Both the cpu and `arch`
  initialize their memories from the *same* top-level `init_mem`/`init_imem`.
  Do not have `arch` read the cpu's mutable memory at init — that creates a
  spurious interference (posedge writes cpu.mem, which the initializer would
  observe). Leaving them uninterpreted proves correctness for every program.

- **Auxiliary trace invariants are mandatory.** The `st(now)=arch` invariants
  alone leave `st(T)` for `T<now` free; the consistency + step-relation
  invariants (step 4) are what make lagging-stage comparisons sound.

- **With unified memory, decoded fields depend on `mem`, so use `old`.** If
  instructions are fetched from the same `mem` as data (no separate `imem`),
  then `fetched`, and everything decoded from it (`mem_addr`, `target`, ...),
  is a function of `mem`. A store mutates `mem` mid-`step`, so a self-modifying
  store re-derives a *different* `mem_addr`/`target` afterward. Read them via
  `old`: `ddirty(old mem_addr) := true`, `pc := old target`.

- **Packing with `concat`.** `concat` is variadic, so a packed cache line is
  built in one shot: `concat(full, dirty, hi_addr, data) : cline` (assign to a
  `cline`/`bv[22]`-interpreted type; ascribe the result). Decode fields with
  `bfe`. A `concat` is given bit-vector semantics only when every argument sort
  *and* the result sort is a bit-vector and the argument widths sum to the result
  width; otherwise it is uninterpreted (still sound by congruence) and a width
  mismatch warns rather than crashing. Two consequences: (1) each `concat`
  argument's sort must be pinned — a bare `bfe[...]` inside a `concat` needs an
  ascription like `(bfe[4][7](pc):nib)`, since the `:cline` on the whole `concat`
  does not constrain the argument widths; (2) inside an isolate closed
  `with addr,opc` (so `word` is not interpreted there), a `concat` returning
  `word` is left uninterpreted — which is exactly what you want for the trace's
  recorded values.

- **Debugging CTIs: use `shrink=false`.** Counterexample generation can be very
  slow; `shrink=false` skips minimization. `trace_dir=<dir>` dumps a CTI for
  *every* failing check at once; `ivy replay <file>.a2g` prints it. A CTI whose
  state is impossible (e.g. `st(0).error = true`, or a cache line at the wrong
  index) means a missing *structural* invariant — add the fact that rules it
  out, don't weaken the property.

## Data hazards, control hazards, speculation

- **Data hazard → stall.** Detect when an operand register matches an older
  in-flight writer; stall the reading stage (its tag does not advance, a bubble
  enters the stage below). Operand correctness then follows from the trace
  step relation — no extra invariant needed.

- **Control hazard, no speculation** (`5stage_cpu_ref`): stall fetch while a
  branch is unresolved, so the trace only ever steps on the correct path. You
  need the fact `branch in EX -> ID slot empty` (rules out fetched-past-branch
  states) and the PC-during-stall invariant (`pc = st(now-1).pc + 1`, the
  fall-through).

- **Speculation** (`5stage_bp_cpu_ref`): add a ghost **shadow** bit per stage
  (+ a `spec_wrong` fetch-stream bit). At fetch, compare the prediction against
  the *true* outcome from the trace (`st(now).take_branch`); on agreement call
  `trace.step`, on disagreement stop stepping and mark subsequent fetches
  shadowed — so the trace never backtracks. Relax the per-stage data invariants
  to hold only when `~shadow`. The core obligation is *shadowed state is never
  committed*: prove `~(e_valid & e_shadow)`, `~(m_valid & m_shadow)`,
  `~(w_valid & w_shadow)` (a mispredicted branch resolves in EX and squashes
  younger instructions before MEM/WB) and `EX holds a mispredicted branch -> the
  ID instruction behind it is shadowed`. Treat the **predictor as an
  unconstrained external input** (`import wire predicted_taken : bool`);
  correctness is independent of the prediction values.

## Caches, incoherence, multi-cycle memory

The `5stage_cache_cpu_ref` example goes further: unified memory (fetch from the
same `mem` as load/store), separate non-coherent I- and D-caches, a `FLUSH`
instruction, and a two-cycle memory. This is the one design where the
**reference model itself changes** — worth studying if your target has caches,
weak memory, or any "software must synchronize" contract.

- **Model the incoherence in the ISA, then relax.** Add architectural state that
  captures the hazard: here `ddirty(A)` (set by store, cleared by `FLUSH`) and a
  sticky `error` set when an instruction is fetched from a dirty address. Then
  guard *every* implementation-vs-reference invariant by `~st(now).error`: once
  the program executes stale code, you no longer require the CPU to match. This
  `~error` relaxation is the correctness statement for an incoherent machine.

- **Caches are pinned by local invariants, relative to the trace at the stage
  that owns them** (`st(mcommit)` for the D-cache in MEM): dirty line ⇒ dirty in
  the reference; present line ⇒ holds the reference value; not-dirty address ⇒
  main memory holds the reference value; I-line not dirty ⇒ holds the reference
  value. Same reference-tagging style, one fact per cache property.

- **Direct-mapped geometry: keep only `hi_addr` in the tag.** If a line stores
  only the high address bits (not the full address), the address it caches is
  structurally `concat(hi_addr, index)`, always at its own index, so no "line is
  filed at the right index" invariant is needed. (If you instead store a full
  address in the tag — e.g. to dodge a `concat` — you *do* need the structural
  invariant `valid(I) -> bfe[0][3](tag(I)) = I`, or the prover imagines a line
  under the wrong index and writes a victim back to a bogus address.)

- **`FLUSH` + fetch stall re-establish coherence.** `FLUSH A` writes back the
  dirty D-line and evicts `A` from both caches; fetch stalls while a `FLUSH` is
  in ID/EX/MEM so nothing behind it is fetched until it has taken effect. The
  "visibility" lemma you might expect to need (dirty@MEM & clean@IF ⇒ FLUSH in
  flight) turned out *not* to be needed as an explicit invariant — the prover
  derived fetch-correctness from the trace step relations + cache invariants +
  the stall. Try without it first.

- **Multi-cycle memory costs no new invariants.** A fill that takes extra cycles
  is just a longer stall, and the "stall ⇒ tag holds" discipline already covers
  it: the stalled stage's tag stops advancing, no `trace.step` is issued, and
  every per-element invariant is preserved across the stall for free. Model the
  memory latency as additional stall conditions folded into the existing
  stage-stall/bubble logic; don't try to verify the memory's own timing (leave
  that to a downstream timing tool).

## Preparing the model for ivy_to_rtl

The datapath must be free of ghost/abstract constructs:

- **Keep all ghost updates in `specification`.** Tag counters, shadow bits, and
  `trace.step` go in the ghost `after posedge` inside `specification { }`, never
  in the datapath `after posedge` — otherwise the cpu is seen writing
  `trace.st` and translation reports an interference error. (Read the real
  validity bits in that ghost monitor via `old` so it is insensitive to monitor
  ordering.)

- **In the MEM stage, read before you write.** Latch the load value
  (`w_val := mem(m_addr)`) *before* performing the store (`mem(m_addr) :=
  m_store`). A MEM instruction is a load or a store, not both, so this is
  behavior-preserving, and it keeps the load a function of the *current* memory
  — otherwise `w_val` depends on `new_mem`, which has no RTL form.

- **No uninterpreted functions in the datapath.** An arbitrary function used in
  hardware logic (a branch predictor `predict(pc)`) has no RTL realization;
  expose it as an `import wire` input instead.

- **State arrays must be point-written.** Cache/memory arrays translate to RTLIL
  memories, so every write must be to a single index (`dcache(idx) := ...`),
  never a whole-array assignment in the clock logic (that has no single-cycle RTL
  form). Power-on `after init` may assign the whole array a constant
  (`valid(I) := false`) or a per-index function — that becomes a `$meminit`.
  Writing an array in several sequential branches of one clock action is fine
  (each is a point write); it composes to the memory's write port.

- Translate with `ivy_to_rtl <file>.ivy` and sanity-check the RTLIL with
  `yosys -q -p "read_rtlil <file>.il"`.

- **Equivalence-check against a golden model (optional, strong).** Because the
  emitted RTL is real hardware, you can cross-check it against an independent
  hand-written model. `references/cpu_golden.sv` is a SystemVerilog transcription
  of the cache-CPU datapath with register/memory names matching the Ivy model,
  and `references/cpu_equiv.ys` proves combinational (per-cycle) equivalence in
  yosys: `equiv_make` pairs registers/memories by name, `memory_map` expands the
  memories, and `equiv_induct` proves the two compute the same next state from
  any equal state. (Tie `rst=0` to compare the datapath, since ivy_to_rtl models
  `after init` as a per-register synchronous-reset mux the golden model need not
  reproduce.)
