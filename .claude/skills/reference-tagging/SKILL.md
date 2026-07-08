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

`references/` contains three worked, fully-verified examples that this skill is
distilled from — read the one closest to your target before writing code:

- `pipe_cpu_ref.ivy` — 2-stage pipeline (the tutorial base case).
- `5stage_cpu_ref.ivy` — standard 5-stage (IF/ID/EX/MEM/WB) with data-hazard
  stalls and non-speculative branches.
- `5stage_bp_cpu_ref.ivy` — 5-stage with a speculative branch predictor (shadow
  bits).
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

- Translate with `ivy_to_rtl <file>.ivy` and sanity-check the RTLIL with
  `yosys -q -p "read_rtlil <file>.il"`.
