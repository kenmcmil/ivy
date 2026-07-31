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

`references/` contains the worked, fully-verified examples this skill is
distilled from (the first four below); read the one closest to your target before
writing code. `dual_issue_cpu_ref.ivy` is a fifth, work-in-progress example
(under `doc/examples/hardware/`) demonstrating component isolation:

- `pipe_cpu_ref.ivy` — 2-stage pipeline (the tutorial base case).
- `5stage_cpu_ref.ivy` — standard 5-stage (IF/ID/EX/MEM/WB) with data-hazard
  stalls and non-speculative branches.
- `5stage_bp_cpu_ref.ivy` — 5-stage with a speculative branch predictor (shadow
  bits).
- `5stage_cache_cpu_ref.ivy` — adds I/D caches, a `FLUSH` instruction, and a
  multi-cycle memory; the reference is extended with `ddirty`/`error` to model
  cache incoherence (see "Caches, incoherence, multi-cycle memory" below).
- `dual_issue_cpu_ref.ivy` (in `doc/examples/hardware/`; **work in progress**
  toward dual-issue fetch) — widens the I-cache line to two words and factors the
  whole I-cache (array + fill state machine + its data invariant) into a nested
  `cpu.ic` sub-isolate proved *locally*. `cpu.ic` is fully verified, its
  fill-input coherence is discharged in the top isolate, and the emitted RTL
  simulates a real two-word fill; see "Isolating a component's proof", "Common
  hardware design issues", and "A safety proof is not a live design" below.
- `reference_tagging.md` — the prose writeup of the method.

## The three ingredients

1. **ISA model** (`module isa_model(init_mem, init_imem)`): the architectural
   state (`pc`, `rf`, `mem`, `imem`) as `var`s, the per-instruction
   intermediate values as **temporary variables** (`var`s holding no
   architectural state) computed by an `action prepare`, and one `action step`
   that consumes them to advance the architectural state. One instruction is
   `prepare; step`.

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

2. **Write `isa_model`.** State as `var`s. Intermediate values as **temporary
   `var`s** (`var opcode : opc`, `var a_val : word`, `var take_branch : bool`,
   ...), *computed* by an `action prepare` (`opcode := fetched<<15:13>>;
   a_val := rf(ra); take_branch := (opcode=6)&(a_val=0); ...`). `after init` sets
   `pc`, zeroes `rf`, and loads `mem(A) := init_mem(A)`, `imem(A) :=
   init_imem(A)`. `action step` executes one instruction, reading the temporary
   `var`s directly (they already hold the pre-state values, so no `old` is
   needed — see gotchas) and advancing the PC with `if take_branch { ... }`.

3. **Write the `trace` isolate.** `instance arch : isa_model(init_mem,
   init_imem)`; `instance tag : unbounded_sequence`; a `state_t` struct with the
   architectural state *and every intermediate value*; `var now`, `var st`; an
   `action current` that snapshots `arch` into a `state_t`; `action step = {
   arch.step; arch.prepare; now := now.next; st(now) := current }`; `after init
   { now := 0; arch.prepare; st(now) := current }`. The `arch.prepare` call
   after each `arch.step` (and in the initializer) recomputes the temporaries in
   the new state before it is recorded, so every trace entry's intermediate
   values are the correct decode of *its own* architectural state. Close the
   isolate with `with addr,opc` (see gotchas).

4. **Trace auxiliary invariants** (boilerplate — mirror the ISA transition over
   recorded entries; an LLM can generate these from `isa_model`):
   - `st(now).X = arch.X` for every field X.
   - Consistency for *all* recorded entries: `T <= now -> st(T).opcode =
     st(T).fetched<<15:13>>`, `... st(T).a_val = st(T).rf(st(T).ra)`, etc.
   - Step relation between consecutive entries: `succ(T,U) & U <= now ->
     st(U).pc = (st(T).target if st(T).take_branch else st(T).pc + 1)`, and
     likewise for `rf`, `mem`, `imem`. Without these, past entries `st(T)` for
     `T<now` are unconstrained and the cpu proof fails.

5. **Implementation datapath.** Model combinational signals as `wire` +
   `definition`, registers/latches as `var`, memories as `var f(A:addr):word`.
   Each stage decodes its instruction word with the `<<hi:lo>>` bit-select;
   stalls/squashes are ordinary `if`s over the latches.

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

- **Compute the ISA's intermediate values in `prepare`, not as defined
  functions.** Do *not* model the intermediate values as `wire`s (a wire is
  frozen for the whole action) nor as `function`s. A defined `function` is
  re-evaluated whenever its dependencies change, so its value shifts *mid-action*
  as `step` writes `rf`/`mem`; reading the start-of-action value then requires
  the `old` operator on *every* such use (`if old take_branch`, `pc := old
  target`, `ddirty(old mem_addr) := true`), and a single forgotten `old` silently
  reads a post-writeback value and breaks the proof. Instead make the
  intermediate values plain `var`s, set them once in `action prepare` from the
  current state, and have `step` read them directly — no `old` anywhere. The
  `trace` runs `arch.prepare` after every `arch.step` (and in `after init`)
  before recording, so each entry's temporaries decode its own architectural
  state. (This is the current pattern in all four reference examples; earlier
  versions used the `function`+`old` style and repeatedly hit the forgotten-`old`
  bug — which is exactly why the examples were changed.)

- **Use the bit-select / concat sugar; pin the bit-select's result sort.**
  ivy1.8+ writes `bfe[i][j](w)` as `w<<j:i>>` (Verilog-style high:low) and
  `concat(a, ...)` as `a :: ...`; the examples use this sugar throughout. It
  desugars in the parser, so every `bfe`/`concat` note here applies unchanged. A
  bit-select is polymorphic in its result sort: when compared to a numeric
  literal or otherwise unconstrained, ascribe it: `(x<<15:13>>:opc) = 6`. When it
  defines a value of known sort (`wire opcode : opc; definition opcode =
  ir<<15:13>>`) the sort is inferred.

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

- **Unified memory makes the `prepare` pattern especially valuable.** If
  instructions are fetched from the same `mem` as data (no separate `imem`),
  then `fetched` and everything decoded from it (`mem_addr`, `target`, ...)
  depends on `mem`, which a store mutates mid-`step`. With the intermediate
  values as `var`s set in `prepare` *before* `step` runs, a self-modifying store
  cannot re-derive them: `step` reads the pre-state `mem_addr`/`target`/`pc`
  directly (`ddirty(mem_addr) := true`, `pc := target`). (With the older
  `function` style these had to be read as `old mem_addr` / `old target`, and
  this is where the forgotten-`old` bugs were most common.)

- **Packing with `::` (concat).** `a :: b :: ...` (sugar for a variadic
  `concat`) builds a packed cache line in one shot: `((1:bit) :: (0:bit) ::
  hi_addr :: data : cline)` (assign to / ascribe a `cline`/`bv[22]`-interpreted
  type). Decode fields with the `w<<hi:lo>>` bit-select. A concatenation is given
  bit-vector semantics only when every argument sort *and* the result sort is a
  bit-vector and the argument widths sum to the result width; otherwise it is
  uninterpreted (still sound by congruence) and a width mismatch warns rather
  than crashing. Two consequences: (1) each argument's sort must be pinned — a
  bare bit-select inside a concat needs an ascription like `(pc<<7:4>>:nib)`,
  since the `:cline` on the whole concatenation does not constrain the argument
  widths; (2) inside an isolate closed `with addr,opc` (so `word` is not
  interpreted there), a concat returning `word` is left uninterpreted — which is
  exactly what you want for the trace's recorded values.

- **Debugging CTIs: use `shrink=false`.** Counterexample generation can be very
  slow; `shrink=false` skips minimization. `trace_dir=<dir>` dumps a CTI for
  *every* failing check at once; `ivy replay <file>.a2g` prints it. A CTI whose
  state is impossible (e.g. `st(0).error = true`, or a cache line at the wrong
  index) means a missing *structural* invariant — add the fact that rules it
  out, don't weaken the property. `ivy_check check=<isolate>.<invname>` restricts
  to one named invariant, and `ivy_check assume_invariants=false` speeds up CEX
  search by dropping known-true postconditions of called procedures — but it can
  drop assumptions you actually need, so re-confirm a CTI without it.

- **A `definition` can be deadly to Z3 — try inlining it.** A whole-CPU
  invariant that made Z3 return `unknown` (neither proof nor counterexample) was
  traced to a *single* defined function — `il_full(L) = (L<<35:35>>:bit) = 1` —
  whose inlining at its use site made the identical query return instantly.
  Sibling definitions of the same shape were harmless, so there is no clean rule
  yet; but when a proof is mysteriously slow or inconclusive, inlining a suspect
  `definition` is a cheap thing to try before assuming the property is wrong or
  the fragment is undecidable.

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
  ID instruction behind it is shadowed`. **Correctness is independent of the
  prediction values**, so the predictor's logic is not part of the proof — the
  CPU reads `bp.predicted_taken` and Ivy verifies it with that bit left
  arbitrary (see next bullet for how to package the predictor).

- **The predictor is a separate (sub-)isolate, connected by the parent.** Give
  the predictor its own I/O *wires* — inputs `fetch_pc`, `br_valid`, `br_pc`,
  `br_taken`; output `predicted_taken` — and put its logic (e.g. a bimodal
  `bht` of 2-bit counters) in its `implementation` block so it is hidden. In the
  parent CPU, *connect* it with definitions of the child's input wires and read
  its output: `definition bp.fetch_pc = pc`, `definition bp.br_taken = e_take`,
  ..., `definition f_ptaken = f_is_branch & bp.predicted_taken`. The predictor's
  hidden implementation means the CPU is verified with `bp.predicted_taken`
  arbitrary (assume-guarantee); the predictor itself carries no invariants (any
  prediction is correct), so its isolate is discharged trivially. Do *not* have
  the predictor reach into CPU state directly — declare its inputs as wires and
  let the parent drive them (the standard isolate-I/O pattern). This also
  translates cleanly to RTL: `ivy_to_rtl` emits the predictor as a submodule
  (`cpu.bp`) with its `bht` memory.

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
  structurally `hi_addr :: index`, always at its own index, so no "line is
  filed at the right index" invariant is needed. (If you instead store a full
  address in the tag — e.g. to dodge a concat — you *do* need the structural
  invariant `valid(I) -> tag(I)<<3:0>> = I`, or the prover imagines a line
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

## Isolating a component's proof (the two-word I-cache)

`dual_issue_cpu_ref.ivy` widens the I-cache line to two words (so a later
dual-issue fetch can read an even/odd instruction pair) and, more importantly,
factors the *entire* I-cache — the array, the two-word fill state machine, the
field accessors, and the I-cache data invariant — into a nested sub-isolate
`cpu.ic`, so that invariant is discharged **locally**. Reach for this when a
single whole-machine invariant is so large that Z3 returns `unknown` (not a
proof, not a counterexample): confine it to an isolate that holds only the
relevant state, and give/assume just the facts that cross the boundary. (The
project spec is `doc/projects/isolate_icache.md`.)

- **Component-isolate shape (same as the predictor).** `ic` declares its I/O as
  `wire`s — inputs `fetch_addr`, `fetch_addr_valid`, `ifill_data`,
  `ifill_data_valid`, and the FLUSH inputs `flush_addr`/`flush_valid`; outputs
  `fetch_data`, `fetch_valid`, `ifill_addr`, `ifill_addr_valid`, `ifill_busy`.
  It owns its state (`icache` array; `ifill_on`/`ifill_got`/`ifill_miss`). The
  parent drives the inputs with interconnect `definition`s placed in **neither**
  `specification` nor `implementation` (so they reach both RTL and the
  sub-isolate). The shared memory port stays in the parent; `ic` only *requests*
  reads (`ifill_addr`/`ifill_addr_valid`) and consumes the returned word — a
  req/return handshake, so a D-fill and the I-fill still share one port.

- **Every bit-vector type the isolate uses must be in its `with` clause** —
  otherwise `bfe`/constants over it are *uninterpreted* and you get **spurious**
  counterexamples (this cost several rounds). Symptoms: a "two numerals assigned
  same value" warning, or a field taking an impossible value — e.g. the full bit
  of the all-zero line reading 1 (`icline` uninterpreted), or `ddirty`/`mem` step
  relations misbehaving because opcode constants 5/7 aren't distinct (`opc`
  uninterpreted). Fix: list them all — `with this, trace, word, addr, nib, bit,
  icline, itag, opc, tag`. Use **`ivy_show isolate=<name> <file>`** to print an
  isolate's contents *and exactly which invariants it assumes* — the right tool
  for auditing this boundary.

- **Export only what the sub-isolate needs; keep the rest `private`.** Split the
  parent's invariants into interleaved `specification { }` / `private { }` blocks
  (you may have many; ordering is free, so you needn't reorder definitions).
  `cpu.ic` needs only two things from the parent: the **input assumption** (the
  fill word equals the reference at the MEM tag when not dirty — proved in cpu,
  since `ifill_data` is driven from main memory), and the **tag-ordering chain**
  (`commit ≤ mcommit ≤ ecommit ≤ dcommit ≤ now`, which gives `mcommit.next ≤ now`
  when `m_valid`, so the trace's single-step relations apply at the MEM tag).
  Everything else (pipeline match, shadow bits, D-cache coherence) stays
  `private` — still used to prove cpu's own obligations, just not dumped into
  `ic`'s VC, keeping it small.

- **Specify the interface as an abstract protocol over ghost state.** The clean
  way to state a cross-isolate contract is to introduce ghost variables for the
  *protocol state* and write the assumption/guarantee as invariants over them —
  the *same* invariant is a guarantee for one side and an assumption for the
  other. The memory↔I-cache protocol here is deliberately minimal: *memory
  returns `mem` at the address presented on the previous cycle, and that word is
  valid exactly when `ifill_data_valid`* — that is all `icache_input` says. Keep
  the protocol as weak as the proof allows: a stronger, more realistic handshake
  (a "request pending" ghost bit, with the cache obliged to hold the address
  constant while pending) is a design choice you *can* add, not a requirement.
  The weakness is what lets the cache be *defensive* (next bullet) rather than
  forcing memory to promise it returns data only when asked.

- **Design for verification: make the isolate *defensive* instead of adding an
  input assumption.** An isolate treats its inputs as arbitrary, so an
  input combination that "can't really happen" still appears as a (spurious)
  counterexample. You can rule it out two ways: add an *input assumption* the
  parent must prove, or **gate the input inside the isolate** so the bad case is
  harmless. Prefer the gate when it is cheap — it shrinks the interface contract
  and makes the proof robust. Example: a stray `ifill_data_valid` while no fill
  is in progress cannot really occur (the parent only raises it on a read this
  isolate requested), but rather than burden `cpu` with an
  `ifill_data_valid -> filling` guarantee, `ic` simply writes
  `ifill_on & ifill_data_valid` everywhere it consumes the fill word. One AND
  gate of real hardware buys a smaller assume-guarantee contract and a simpler,
  more defensive block. The same spirit drives voiding the fetch bypass and the
  install on a same-cycle FLUSH (below): `ic` self-protects against stale data
  instead of demanding the environment never present it. Weigh the (usually
  tiny) hardware cost against the proof/interface simplification.

- **A pipeline latch on the interface breaks a naive coherence invariant —
  bridge it with a ghost of the delayed value.** The returned fill word is
  `mem(mfa)`, i.e. memory at the address presented *one cycle earlier* (the port
  latches the request address into `mfa`). Stating the input coherence over the
  *current* `ic.ifill_addr` fails: in the parent's abstraction of `ic`,
  `ifill_addr` is a free output, so the solver moves it and the datum no longer
  matches (the CTI shows `ifill_addr` jumping to an unrelated value in the
  post-state). Fix: add a ghost `ifill_addr_old` mirroring the latched address
  (`ifill_addr_old := ic.ifill_addr` every posedge, in `specification` so `ic`
  sees the update logic), and state `icache_input` over `ifill_addr_old` — the
  parent proves it because `mfa` and `ifill_addr_old` latch the *same* previous
  value. The isolate then only has to guarantee it *holds the address stable*
  across the request→response, i.e. `held_addr: ifill_on -> ifill_addr =
  ifill_addr_old`. General move: when a property couples two isolates across a
  pipeline register, introduce ghost state for the delayed value and split the
  obligation at that register.

- **Redefine the FSM's state so the bridging invariant is inductive, instead of
  piling on guards.** `held_addr` was *not* inductive under the first encoding:
  `ifill_addr` changes on the miss→sibling switch and on a flush-reset while
  `ifill_on` still held. Guarding it (`ifill_on & ifill_data_valid -> ...`) still
  failed, because `ifill_data_valid` is a *free input* to the isolate — nothing
  stops the solver asserting it the cycle after the address moved. The fix was to
  change the *meaning* of `ifill_on` to "a fill request went out last cycle",
  giving the fill machine the clean four-state cycle `(off,¬got) -> (on,¬got) ->
  (off,got) -> (on,got) -> (off,¬got)` in which `ifill_addr` never moves while
  `ifill_on` — so `held_addr` holds *unguarded*. Picking the right state
  abstraction is often far cheaper than strengthening a stuck proof. (This
  transition edit also fixed a liveness bug — see "A safety proof is not a live
  design".)

- **Combinational input→output paths need the input assumption in the
  *post*-state.** `ic`'s output guarantee (a valid fetched word is coherent with
  the reference) has a **zero-delay path** from an input (`ifill_data`, the fill
  bypass) to an output (`fetch_data`). Proving the *output* invariant in the
  post-state therefore needs the *input* invariant **in the post-state**, but
  ordinary assume-guarantee only hands you pre-state assumptions. Fix: name the
  input invariant (`invariant [icache_input] ...`) and add **`with icache_input`**
  to the output invariant (`invariant [icache_output] ... with icache_input`).
  This is sound exactly because the dependency is acyclic — the input assumption
  is discharged by the parent independently of the output. Without it the bypass
  case is a spurious counterexample. (This wrinkle applies to any isolate with a
  combinational path from an assumed input to a guaranteed output.)

- **The half-filled line must be a distinct, well-formed state.** With one `full`
  bit per two-word line, a line mid-fill has `full = 0` and holds only its miss
  word (the fill state machine, not a per-word valid bit, records which word is
  live). State this as an invariant (`midfill`: while `ifill_on & ifill_got`, the
  line at the miss index is `~full` and carries the miss word's tag). The `~full`
  part is load-bearing: it is what stops a FLUSH — which only evicts *full* lines
  with a matching tag — from silently clobbering the in-progress fill.

## Common hardware design issues

Verification surfaces genuine design bugs, not only proof-engineering ones. When
designing a cache, **explicitly consider the collision of a fill and a FLUSH (or
any invalidation) on the same address.** A multi-cycle fill reads memory over
several cycles; if a FLUSH of the address being filled lands in that window, the
word in flight — or the miss word already installed — is stale w.r.t. the
freshly-flushed memory, and installing or forwarding it violates coherence. The
two-word I-cache needed three guards, each found from a counterexample:

  1. **Ignore the returned fill word** when a FLUSH this cycle targets the fill
     address (`~(flush_valid & flush_addr = ifill_addr)` on the install).
  2. **Void the fetch bypass** under the same condition, so fetch misses and
     refetches rather than forwarding the stale word. Easy to forget: the install
     and the fetch consume the same returned word by two different routes, so
     both need the guard (the bypass one is what finally closed `icache_output`).
  3. **Refetch the miss word** when a FLUSH hits the already-installed miss word
     of a half-filled line (`flush_addr = ifill_miss -> ifill_got := false`), so
     the machine rereads it from now-current memory. (The CTI showed the stale
     address is `ifill_miss`, the cached word — not `fetch_addr`.)

The general lesson: for any in-flight, multi-cycle operation (fill, prefetch,
write-back), enumerate the invalidations that can occur *during* it and decide,
per case, whether in-flight data must be dropped, re-issued, or is safe.

## A safety proof is not a live design — simulate

Reference tagging proves *safety* (nothing bad relative to the ISA). It says
nothing about *liveness*, and the isolate machinery can hide a dead design.

- **All-invariants-pass does not mean the machine does anything.** The whole
  `cpu.ic` proof passed while the fill state machine was actually *stuck* — a
  missing `(off,got) -> (on,got)` transition meant no fill ever completed, so the
  cache never held a full line. A machine that never leaves a coherent
  idle/half-filled state trivially satisfies every coherence invariant. Adding
  the transition made the fill machine live *and* was the state redefinition that
  made `held_addr` inductive (above) — one edit fixed both.

- **Inductive "probe" invariants are not reachability tests.** Tempted to check
  whether a state is reachable by asserting its negation and seeing if it fails?
  Don't: `ivy_check check=X` assumes *every other* listed invariant in the
  pre-state — including any hand-added probes, even false ones — so the probes
  contaminate each other and the result answers "is X implied by the invariant
  set under one step", not "is state S reachable". Probing `~ifill_got` this way
  falsely suggested the fill machine was unreachable (proof vacuous); it was not.

- **Simulate to settle liveness and non-vacuity — it is the ground truth the
  inductive checker cannot give.** Because the emitted RTL is real hardware, run
  it: `sim_cpu.sh <design> [prog.hex] [cycles] [extra_signals]` emits RTLIL,
  injects a program into `\mem` at the RTL boundary (via `load_program.py`, so
  the program stays *out* of the Ivy source — main memory is uninterpreted, and
  the proof still holds for every program), runs `yosys sim`, and prints the pc
  trace plus any extra signals per cycle. It is generic across same-ISA designs
  with unified memory in `cpu.mem` (it keys only on an 8-bit `pc` and the `\mem`
  array). Passing `"ifill_on,ifill_got,mbusy"` showed the full four-state fill
  cycle firing on every line — proof-positive of liveness that no invariant
  check surfaced. Make a quick simulation a routine companion to the proof.

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
  hardware logic has no RTL realization. Either expose it as an `import wire`
  top-level input, or — better when it is a real component like a branch
  predictor — put it in its own isolate with wire I/O and connect it in the
  parent (see the predictor bullet under "speculation"); its hidden
  implementation is what lets the CPU proof treat its output as arbitrary.

- **State arrays must be point-written.** Cache/memory arrays translate to RTLIL
  memories, so every write must be to a single index (`dcache(idx) := ...`),
  never a whole-array assignment in the clock logic (that has no single-cycle RTL
  form). Power-on `after init` may assign the whole array a constant
  (`valid(I) := false`) or a per-index function — that becomes a `$meminit`.
  Writing an array in several sequential branches of one clock action is fine
  (each is a point write); it composes to the memory's write port.

- Translate with `ivy_to_rtl <file>.ivy` and sanity-check the RTLIL with
  `yosys -q -p "read_rtlil <file>.il"`.

- **Inject the program at the RTL boundary, not in the Ivy source.** Because main
  memory is emitted with no `$meminit` (its init function is uninterpreted), a
  program is supplied for simulation by patching a `$meminit` for `\mem` into the
  netlist — that is what `load_program.py` does, and what `sim_cpu.sh` wraps
  together with `yosys sim` (see "A safety proof is not a live design"). The Ivy
  model — and its proof — stay program-independent.

- **Equivalence-check against a golden model (optional, strong).** Because the
  emitted RTL is real hardware, you can cross-check it against an independent
  hand-written model. `references/cpu_golden.sv` is a SystemVerilog transcription
  of the cache-CPU datapath with register/memory names matching the Ivy model,
  and `references/cpu_equiv.ys` proves combinational (per-cycle) equivalence in
  yosys: `equiv_make` pairs registers/memories by name, `memory_map` expands the
  memories, and `equiv_induct` proves the two compute the same next state from
  any equal state. (Tie `rst=0` to compare the datapath, since ivy_to_rtl models
  `after init` as a per-register synchronous-reset mux the golden model need not
  reproduce.) When the design is hierarchical — e.g. the CPU instantiates the
  predictor submodule `cpu.bp` — make the golden model hierarchical the same way
  (a `bp` submodule instantiated as `bp`) and `flatten` both designs before
  `equiv_make`, so the shared instance name lines the inlined names up (e.g. the
  predictor's `bp.bht` memory pairs by name).
