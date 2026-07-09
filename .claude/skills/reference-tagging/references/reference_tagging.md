---
layout: page
title: Reference tagging
---

Now we will look at a general method of specifying and verifying hardware micro-architectures called "reference taggging".

The idea of reference tagging is to verify a hardware design against an
*executable reference model* -- here, the instruction set architecture (ISA)
-- rather than against a hand-written inductive invariant. We keep, as ghost
state, a *trace*: the sequence of architectural states the ISA passes through
as it executes a program, one entry per instruction. The hardware, meanwhile,
may have many instructions in flight at once, at different stages of
completion. To connect the two, we give each element of microarchitectural
state a *tag*: an index into the trace, naming the instruction that element is
currently working on. We then write, for each element, a simple invariant
saying that its contents equal the corresponding value in the trace *at its
tag*.

The payoff is decomposition. Instead of one large, monolithic invariant that
relates the whole machine to the ISA, we get a small, local invariant for each
microarchitectural element -- each pipeline latch, the register file, the
memories -- expressed directly in terms of the reference trace. Each such
invariant is easy to state and to understand, and (as we will see) they compose
to give the end-to-end correctness result. The same trace model is reused
unchanged across designs of increasing complexity; only the tags and the
per-element invariants change.

We develop the method on three designs, all implementing the same tiny ISA:
a [two-stage pipeline](pipe_cpu_ref.ivy), a
[five-stage pipeline](5stage_cpu_ref.ivy), and a
[five-stage pipeline with a branch predictor](5stage_bp_cpu_ref.ivy).

Two-stage pipeline example
--------------------------

In this section we will consider again the simple 2-stage processor
pipeline model (see [the two-stage pipeline](pipe_cpu.html), whose datapath we
reuse here). We will write a trace
model for the instruction set architecture and relate it to the
content of the pipeline stages using tags, ultimately verifying that
the processor pipeline implements the ISA.


The trace model
===============

The ISA is written as an ordinary state machine, in a module `isa_model`. Its
state is the architectural state -- the program counter, register file, data
memory, and (read-only) instruction memory:

    var pc : addr                 # program counter
    var rf(R:reg) : word          # register file
    var mem(A:addr) : word        # data memory
    var imem(A:addr) : word       # instruction memory (ROM; never written)

The intermediate values that arise while executing one instruction -- the
fetched word, the decoded fields, the operand values read from the register
file, the branch decision -- are written as *defined functions* of the state:

    function fetched = imem(pc)
    function opcode  = bfe[13][15](fetched) : opc
    function a_val   = rf(ra) : word
    function take_branch = (opcode = 6) & (a_val = 0) : bool

These intermediate values will be important later: they are exactly the
quantities the hardware computes in its combinational logic, so recording them
in the trace lets us specify the hardware's internal signals directly.

A note on why these are *defined functions* rather than *wires*. In the
hardware we model combinational signals with wires, whose value is frozen at
the start of a clock cycle and cannot change while the registers update. That
is the wrong behavior for an abstract model. The abstract `step` action is
synchronized to a hardware clock edge, but *within* that action we want the
intermediate quantities to track the state as it changes -- for instance, after
`step` writes the register file, `a_val = rf(ra)` should reflect the new
contents. Defined functions do exactly this: they are re-evaluated whenever the
state they depend on changes. The flip side is that a defined function can
change value in the middle of an action, so when we need the value it had at
the *beginning* of the action we use the `old` operator. In `isa_model`, the
program-counter update reads `old take_branch`, the branch decision as computed
*before* the writeback, so that a load or ALU result written this step cannot
retroactively change whether the branch was taken:

    after step {
        # ... execute / writeback, updating rf or mem ...
        if old take_branch {
            pc := target            # redirect to the branch target
        } else {
            pc := pc + 1
        }
    }

Finally, note that the initial contents of the instruction and data memories
are *parameters* of the ISA model (`isa_model(init_mem, init_imem)`). This lets
us align the abstract execution with the hardware for *any* initial memory
contents: both the reference and the implementation start from the same,
arbitrary, `init_mem`/`init_imem`, so the proof holds for every program rather
than one hard-coded program.

On top of `isa_model`, the `trace` isolate records an entire ISA execution, one
step at a time. It instantiates the ISA as `arch`, and an abstract sequence
type `tag` to index the trace. The trace itself is an array `st` of recorded
states and a pointer `now`:

    var now : tag                 # length of the trace so far
    var st(T:tag) : state_t       # the recorded states

Each entry `st(T)` is a `state_t` struct that records not only the
architectural state (pc, rf, mem, imem) but also all of the intermediate values
(opcode, rd, ra, rb, target, a_val, b_val, mem_addr, take_branch) at that point
in the execution. The trace provides a *ghost* action `step`, meant to be
called from the hardware model when the hardware issues an instruction:

    action step = {
        arch.step;                # advance the ISA by one instruction
        now := now.next;          # extend the trace
        st(now) := current        # record the new architectural state
    }

`step` executes one ISA instruction and appends the resulting state to the
trace, advancing `now`, which always points at the state reached after all
instructions issued so far. Like the shared memory initialization, `step` is
there purely to align the abstract and concrete models: it lets us prove that
every hardware execution can be read off as a legal ISA trace.

To prove properties of the hardware, the trace needs a number of *auxiliary
invariants* about itself. It is not enough that the most recently recorded
state, `st(now)`, matches `arch`; the pipeline compares lagging stages against
*earlier* trace entries, so every recorded entry must be a faithful ISA state.
Concretely, we assert that

* each recorded state's intermediate values are the correct decode of its own
  architectural state (e.g. `st(T).opcode = bfe[13][15](st(T).fetched)`), and
* consecutive recorded states are related by one ISA step: `st(T+1)` is the
  result of executing `st(T)`'s instruction (the PC advances or branches, the
  register file and memory are updated according to the opcode).

These "the trace is a valid execution history" invariants are boilerplate --
they simply restate the ISA's transition relation over recorded entries -- and
can easily be generated from the ISA model (for instance, by an LLM).

The implementation
==================

The implementation of the pipeline is the same datapath as in the previous
example. To verify it, we augment its state with *ghost* variables: a *tag* for
each pipeline stage, pointing into the trace at the instruction that stage is
working on. In the two-stage machine there is a tag for the fetch stage
(`f_tag`) and one for the execute stage (`x_tag`). Each clock edge, we advance
the tags to follow the instructions down the pipe, and we call the abstract
`step` action exactly when the hardware issues a valid instruction:

    after posedge {
        x_tag := f_tag;                    # the X stage takes the F stage's instruction
        if ~take_branch {
            f_tag := f_tag.next;           # the F stage advances only if not squashed
            trace.step                     # ... and a new instruction is issued
        }
    }

Whether a stage's tag advances depends on the stage's own behavior. Here, on a
taken branch the instruction the fetch stage is holding lies in the branch's
shadow and will be squashed, so we neither advance `f_tag` nor issue it to the
trace. In more elaborate machines a tag also fails to advance when a stage
stalls. All of this ghost code -- the tags and the `trace.step` calls -- exists
only for the proof, to show the CPU implements the ISA; it is confined to the
specification and does not appear in the generated hardware.

With the tags in place, the correctness of each pipeline element is a single
invariant relating it to the trace at its tag. For the two-stage machine:

    invariant ~take_branch -> pc = trace.st(f_tag).pc
    invariant ir_valid     -> ir = trace.st(x_tag).fetched
    invariant rf(R)  = trace.st(x_tag).rf(R)
    invariant mem(M) = trace.st(x_tag).mem(M)
    invariant imem(M) = trace.st(x_tag).imem(M)

That is: the fetch PC is the PC of the trace entry at `f_tag`; the
execute-stage instruction register holds the instruction fetched at `x_tag`;
and the register file and memories match the architectural state just before
that instruction executes. Notice how the *intermediate* values recorded in the
trace are exactly what we need to specify the hardware's pipeline registers --
for the deeper pipelines they let us pin down partially-computed results
(ALU outputs, load addresses) against the reference.

A slightly subtle point: because this CPU currently has no outputs, these
invariants only constrain internal microarchitectural state. That is,
nonetheless, the substance of the proof -- once each stage is pinned to the
trace, exposing a correct output is trivial. We could add an output port (say,
the retiring PC or a memory-write interface) and immediately prove it agrees
with the ISA model, since the state feeding it is already related to the trace.

A five-stage pipeline
---------------------

As the microarchitecture gets a little more complex, we can start to
see the advantage of the trace model in expressing the proof.

The [five-stage pipeline](5stage_cpu_ref.ivy) (IF, ID, EX, MEM, WB) reuses
*exactly the same* `isa_model` and `trace` isolate -- the reference does not
change when the implementation does. What changes is the set of tags and their
invariants. Now there are more instructions in flight, so we track, for each
stage boundary, a tag counting how many instructions have passed it
(`commit`, `mcommit`, `ecommit`, `dcommit` for the WB, MEM, EX and ID
boundaries). The pipeline occupancy is a contiguous run of trace indices, which
we capture with a few structural invariants (each count is the next plus one
when the intervening stage holds a valid instruction), and then the same style
of per-element invariants ties the register file to `st(commit)`, the data
memory to `st(mcommit)`, and each latch's contents to the trace at its own tag.

This design reads operands in EX and writes back in WB, so a dependency on an
instruction still in MEM or WB is a data hazard, resolved by *stalling* EX --
which simply means the stalled stage's tag does not advance that cycle. Because
operands (and the branch condition) are read in EX, a branch also resolves in
EX; to keep the trace free of wrong-path instructions this version does not
speculate -- it stalls fetch while a branch is unresolved, and so issues
`trace.step` (advances `now`) only for instructions it is certain lie on the
correct path. The auxiliary trace invariants carry over unchanged; the whole
increase in complexity is absorbed by the tags and the local invariants.

Handling speculation
--------------------

Now we add a [branch predictor](5stage_bp_cpu_ref.ivy) to the CPU.

With a predictor the machine fetches *speculatively*: it guesses each branch
and keeps fetching, so instructions on a mispredicted path enter the pipeline
and must later be squashed. The trace, however, must record only the correct
path. We reconcile the two with a ghost *shadow* bit on each stage (and on the
fetch stream), meaning "this instruction was fetched behind a mispredicted, not
yet resolved, branch."

The shadow bit is derived from the trace model. When the fetch stage issues a
non-shadowed instruction -- one on the correct path, at tag `now` -- the ghost
code compares the predictor's guess against the *true* branch outcome, which it
reads from the trace as `st(now).take_branch`. If they agree, the fetch stays
on the correct path and we call `trace.step` as before. If they disagree, the
prediction was wrong: we do *not* call `trace.step`, and we mark subsequent
fetches shadowed. In this way the trace only ever steps along correct branches,
and never has to be rolled back.

The main proof obligation is then to guarantee that shadowed pipeline state is
never committed to architectural state -- a squashed instruction must not write
the register file or memory. This holds because the true branch condition is
computed in EX (before MEM and WB): the instruction carries its prediction down
the pipe, EX compares it against the correct outcome, and on a mismatch the
younger, shadowed instructions are squashed before they reach MEM. The
invariants make this precise: a stage's contents are required to match the
trace only when it is *not* shadowed, and structural invariants establish that
a valid shadowed instruction can only ever sit in the ID stage (everything
further down has been squashed), so nothing shadowed reaches the register file
or memory.

Finally, note that we have not actually implemented the branch predictor. We
treat it as an external input to the CPU -- a `predicted_taken` wire the
pipeline reads each cycle -- and leave it completely unconstrained. This works
because the correctness of the CPU does not depend on the *values* the
predictor produces: a good predictor improves performance, but any prediction
whatsoever yields a correct execution. (Later we can implement a predictor as a
separate isolate that drives this input, and Ivy will not need to look at its
logic when verifying the CPU.)

Caches and memory incoherence
-----------------------------

Our last design adds instruction and data caches
([5stage_cache_cpu_ref.ivy](5stage_cache_cpu_ref.ivy)). This is a bigger step,
because it changes the *reference model* -- the first time we have had to do so.

Memory is now *unified*: there is a single `mem`, and instructions are fetched
from the same memory that loads and stores use. The implementation keeps an
instruction cache and a data cache that are *not* kept coherent -- a
direct-mapped, write-back D-cache for loads and stores, and a read-only I-cache
for fetch. So a store can leave a new value in the D-cache (or, after a
write-back, in main memory) while the I-cache and the fetch path still see the
old bytes. Real machines expose exactly this, and require software to issue an
explicit synchronization (here, a `FLUSH` instruction) before executing
freshly written code.

We reflect this in the ISA with two new pieces of architectural state: a
per-address dirty bit `ddirty(A)`, set by a store to `A` and cleared by a
`FLUSH` of `A`, and a sticky `error` bit, set when an instruction is fetched
from an address that is currently dirty. `error` models "the program did
something whose result is not guaranteed" -- it executed stale code. The trace
model carries these like any other field, with the boilerplate step-relation
invariants (a store sets the bit, a flush clears it, a dirty fetch latches
`error`). One subtlety: because memory is now unified, the decoded fields --
including the store address `mem_addr` and the branch `target` -- are functions
of `mem`, so a self-modifying store can change them mid-step. The ISA therefore
computes them with `old` (`ddirty(old mem_addr) := true`, `pc := old target`),
reading the pre-store values.

The key move in the specification is a *relaxation*: every invariant relating
the implementation to the reference is guarded by `~trace.st(trace.now).error`.
Once the reference has executed a stale fetch, we no longer require the CPU to
match it. Since `error` is sticky and `now` is the largest recorded tag,
`st(now).error` holds exactly when *some* instruction in the executed prefix has
erred, so the guard says "as long as the program has not yet gone wrong, the CPU
implements the ISA." This is the substance of the correctness statement for an
incoherent machine.

The caches themselves are pinned to the reference by *local* invariants, in the
same reference-tagging style, all relative to the trace state at the MEM stage
(`st(mcommit)`):

* a dirty D-cache line's address is dirty in the reference;
* a present D-cache line holds the reference's value;
* an address that is not dirty in the D-cache has the reference's value in main
  memory;
* an I-cache line whose address is not dirty holds the reference's value.

Together these say the *effective* memory -- D-cache where present-and-dirty,
else main memory -- always equals the reference memory (until an error), and the
I-cache agrees wherever it has not gone stale. Each line is a packed bit-vector
`[21] full | [20] dirty | [19:16] hi_addr | [15:0] data`, built with `concat` and
decoded with `bfe`. Because the tag holds only `hi_addr` (not the full address),
the address a line caches is structurally `concat(hi_addr, index)`, so it is
always at its own index -- no extra "line is filed at the right index" invariant
is needed.

`FLUSH A` is what re-establishes coherence: in the MEM stage it writes the
D-cache line for `A` back to main memory if it is dirty, then evicts `A` from
*both* caches, so the next fetch of `A` misses and refills from up-to-date
memory. For that to be enough, no instruction behind a `FLUSH` may be fetched
until the `FLUSH` has done its work, so fetch stalls while a `FLUSH` occupies
ID, EX or MEM. Interestingly, the "visibility" property one might expect to need
as an explicit invariant -- *if an address is dirty at MEM but clean at IF then
a `FLUSH` of it is in flight* -- did not have to be stated: the prover derives
the fetch-correctness obligation from the trace step relations, the cache
invariants, and the fetch-stall discipline. The coherence argument stays
entirely in the local per-element invariants.

Multi-cycle memory
------------------

Finally, main memory is made multi-cycle: a read fill takes two clock cycles (an
initiating cycle and a busy cycle in which the value arrives and is bypassed),
and write-backs are instant. A fill controller (a `busy` bit plus the fill
address) serves one fill at a time, giving data-cache fills priority over
instruction-cache fills. An I-cache miss stalls the fetch stage; a load miss
stalls the memory stage and the stages behind it, draining a bubble to
write-back.

What is notable for verification is how *little* this costs. The proof needs no
new invariants at all: the reference-tagging discipline already has each stage's
tag hold when the stage stalls, so the extra fill-stall cycles are just more of
the same -- the tags stop advancing, no `trace.step` is issued, and every
per-element invariant is trivially preserved across the stall. The memory's own
timing (the two-cycle handshake) is deliberately *not* verified here; the intent
is that a downstream timing tool checks it, while Ivy checks that the pipeline
computes the right architectural result regardless of how many cycles a fill
takes.

RTL
---

All four designs translate to RTL with `ivy_to_rtl`, because the datapath is
kept free of ghost state (tags, shadow and dirty bits used only in the proof
live in `specification` blocks) and uses only point writes to the state arrays.
Each cache is a single memory of packed 22-bit lines; a line is assembled with
`concat` and its fields read with `bfe`, so in RTL it is one narrow memory per
cache -- a direct-mapped cache. (This uses `concat`'s variadic form,
`concat(full, dirty, hi_addr, data)`; a `concat` is given bit-vector semantics
only when every argument and the result are bit-vectors and the argument widths
sum to the result width, and is otherwise treated as uninterpreted.)
