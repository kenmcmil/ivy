+++
title = "Verifying a pipeline against its ISA in Ivy, and translating it to RTLIL"
date = "2026-07-13"
author = "Kenneth McMillan"
summary = "How to model a pipelined CPU in Ivy, prove it implements its ISA for every program, and translate the result to Yosys RTLIL — with an AI assistant generating the RTL and the proof."
tags = ["ivy", "formal-verification", "hardware", "yosys"]
ShowToc = true
TocOpen = false
+++

This post describes how to develop formally verified synchronous
hardware in a language called [Ivy](https://kenmcmil.github.io/ivy/): how to model a
design, how to prove it implements its instruction-set architecture
(ISA) for every program, and how to translate the result to Yosys
RTLIL for equivalence checking, simulation, and synthesis. The intended reader is a designer
who is familiar with Yosys but new to Ivy.

The design process has three parts:

1. A human designer provides an ISA model and a natural language design description,
2. An AI assistant generates the RTL design and the proof in Ivy's language, and
3. The Ivy formal verification tool checks the correctness of the proof.

Because verification is formal, algorithmic and end-to-end, this process
allows us to make maximum use of generative AI in creating a design while
minimizing the risk of design error escapes. 

In this post, we will detail the development of a sequence of tutorial CPU design examples. While the method we apply here is fairly general, scaling up to larger more complex designs will likely require more advanced techniques for decomposing the proof into manageable parts. Ivy's support for hardware design is in the early stages of development, so our intent here is to give a preview of what might be accomplished using Ivy in the future, rather than a description of a mature tool.

All code below is excerpted from complete examples in the Ivy repository. Links to the
full files are collected at the end.

## Why Ivy: exploiting the strengths of SMT solvers, avoiding their weaknesses

End-to-end formal verification means proving logically that a full design does what its
specification says, for all inputs and all time, rather than checking a handful
of properties up to a bounded depth. This is challenging primarily because the
underlying reasoning is hard to automate reliably. Modern SMT solvers are the
engine of many formal verification tools and they have a characteristic profile. They are
fast, complete, and predictable on certain theories. For example, quantifier-free formulas
over bit-vectors, arrays, uninterpreted functions with equality, and linear
arithmetic are all decidable, and modern solvers dispatch them routinely.
They become unpredictable, and often simply fail to terminate, on other inputs.
Formulas with arbitrary quantifier alternation, nonlinear integer arithmetic, and undisciplined
combinations of theories often result in an inconclusive answer or a timeout.
In the first regime, we can rapidly iterate to a correct proof. In the second, we quickly become
bogged down in debugging solver failures.

Ivy is designed around this distinction. Its purpose is to make end-to-end
functional verification tractable by keeping the verification conditions it
generates in a form that SMT solvers handle well. It does this in two ways. First, the modeling and specification
language steers you toward a decidable logical fragment. Ivy warns when proof obligations
would fall outside this fragment. Second, Ivy structures proofs so that each verification
condition is small and local: designs are decomposed into *isolates* -- modules that are
verified separately against formal contracts. Correctness is
expressed as many local invariants rather than one global one. When a proof
attempt fails, Ivy returns a concrete counterexample to induction — a behavioral trace
in which some invariant is not preserved. These counterexamples are critical to the proof
process, providing the guidance needed to correct the proof and iterate to convergence. 

After a design is proved correct, Ivy can translate it into RTLIL. At
this point, a traditional ASIC or FPGA flow can take over. We can also
check equivalence of the Ivy design with a golden RTL model written in
a traditional HDL such as SystemVerilog. While maintaining
representations of the same design in two languages might seem
burdensome, we will see that AI agents can quickly perform translations
between the two languages, making it straightforward to keep the models
in sync.

## Hardware in Ivy: registers, wires, clocks

A synchronous design is a set of registers, updated on a clock edge, connected
by combinational logic that settles between clock edges. Ivy models this with three
constructs:

- **`var`** — a state variable: a register, or, for an array type, a memory.
- **`wire`** — a defined combinational signal, a non-cyclic function of state
  and of other wires. During a clock action a wire's value is *frozen* at its
  pre-edge value, modeling the behavior of combinational logic settling before
  the edge.
- **`export action posedge`** — a clock edge, modeled as an action invoked by
  the environment. Register updates are given in an `after posedge` code block,
  reset behavior in an `after init` block.

Here is a complete 8-bit accumulator with one input `x`, one output `sum`, and one
register `acc`:

```ivy
#lang ivy1.8
type word
interpret word -> bv[8]

export action posedge

isolate accum = {
    import wire x : word       # top-level input
    export wire sum : word     # top-level output
    var acc : word
    after init    { acc := 0 }
    after posedge { acc := acc + x; }
    definition sum = acc
}
```

The type `bv[8]` represents a bit vector of width 8. Notice that the
declaration of type `word` has two parts. The first just declares `word` as a
type. The second says to *interpret* `word` as an 8-bit vector type.
This is an important feature of Ivy for making proof automation
tractable.  If we really need to know that words are 8-bit vectors to
prove something, we can use this fact. Otherwise, we can forget it and
treat `word` as an *uninterpreted*: just a set of values with no
additional semantics. This change can make an otherwise undecidable
proof obligation decidable. Separating 8-bit variables into different named types
can also have this effect (as well as providing stronger type checking). 


```bash
$ ivy_to_rtl accum.ivy
```

yields a single RTLIL module in which `acc + x` is an `$add`, `acc` is a `$dff`,
and the `after init` value becomes a reset mux on the flop's `D` input. Designs
are hierarchical: nested Ivy objects (*isolates*) become submodules, wired
together by definitions in the parent. Hierarchical designs represented in Ivy
can be simulated and synthesized using Yosys. For more details on the path from
Ivy to RTL see the Ivy documentation on 
[hardware design basics](https://kenmcmil.github.io/ivy/examples/hardware/basics.html).

## A pipeline and the verification problem it poses

Consider a small pipelined CPU implementing a seven-opcode ISA (ALU operations,
load-immediate, load, store, branch-if-zero) over a 16-bit word, an 8-bit
program counter, and an eight-entry register file. The two-stage version
([`pipe_cpu.ivy`](https://github.com/kenmcmil/ivy/blob/master/doc/examples/hardware/pipe_cpu.ivy))
fetches in stage F and executes in stage X, with a pipeline register between
them. Details on the simple two-stage pipeline can be found [here](https://kenmcmil.github.io/ivy/examples/hardware/pipe_cpu.html).

The state of the CPU is represented by these variables:

```ivy
    var pc : addr                 # program counter
    var rf(R:reg) : word          # register file
    var mem(A:addr) : word        # data memory
    var imem(A:addr) : word       # instruction memory (ROM; never written)

    # pipe registers
    var ir : word                 # instruction being executed in X
    var ir_valid : bool           # false => bubble (nothing to execute)

```

The variable `rf`, representing the register file is a map from type `reg` (three bits) to
type `word` (16 bits). In RTL, this map becomes a memory. The data memory `mem` and instruction
memory `imem` are similar. Variables of type `bool` in Ivy become 1-bit registers in RTL. 

We use wires to represent combinational logic in the CPU. For example,
here is the instruction fetch, decode and operand fetch logic:

```ivy
# F stage

wire fetched : word = imem(pc)   # fetched instruction

# X stage

wire opcode : opc = ir<<15:13>>
wire rd : reg = ir<<12:10>>      # destination operand
wire ra : reg = ir<<9:7>>        # A source operand
wire rb : reg = ir<<6:4>>        # B source operand
wire target :addr = ir<<7:0>>    # branch target

wire a_val = rf(ra)              # A operand value
wire b_val = rf(rb)              # B opernd value

# branch-on-zero opcode is 6
wire take_branch : bool = ir_valid & (opcode = 6) & (a_val = 0) 
```

The state update occurs in an `after posedge` block. 

```ivy
after posedge {
    if ir_valid {
        if opcode = 1 { rf(rd) := a_val + b_val; }  # ADD
        else if opcode = 2 ...
    }
    if take_branch {
        pc := target; ir_valid := false;   # redirect, squash shadowed inst
    } else {
        pc := pc + 1; ir := fetched; ir_valid := true;
    }
}
```

If X has a valid instruction, we execute it based on the opcode in `ir`. 
The branch is resolved in X, one cycle after it is fetched, so by the time the
machine knows a branch is taken it has already fetched the next sequential
instruction into the branch's shadow, and that instruction must be squashed.

This is an example of a control hazard. It is also what makes a pipeline hard to
verify: at any instant the machine holds several instructions at different
stages of completion, some of which may be discarded. The pipeline is correct if it behaves like the ISA — a sequential, one-instruction-at-a-time
reference — for every program. It is possible to state correctness as single monolithic inductive
invariant relating the pipelined state to the ISA state using a flushing function. However, this is exactly the sort of complex global assertion that
strains an SMT solver. The design pattern below keeps the invariant small and local, and
therefore within the solver's reliable range.

## Reference tagging

The design pattern is called *reference tagging*:

1. Write the ISA as an executable state machine, `isa_model`. This model simply computes the
   effect of executing one instruction on the architectural state.
2. Construct an execution trace: the sequence of architectural
   states the ISA passes through as it executes the program, one entry per
   instruction. This is a *ghost* variable, meaning it is part of the proof but doesn't affect the hardware. 
3. Tag each microarchitectural element with an index into the trace — the
   instruction that element is currently working on.
4. Prove, for each element, a single invariant stating that its contents equal
   the trace value at its tag.

Ghost state exists only to state and check the specification. In Ivy, it is confined to
`specification` sections and removed before translation to hardware.

### The ISA model

The ISA's architectural state — PC, register file, memory, instruction
ROM — is represented by `var` declarations. In our simple CPU, we have:

```ivy
    var pc : addr                 # program counter
    var rf(R:reg) : word          # register file
    var mem(A:addr) : word        # data memory
    var imem(A:addr) : word       # instruction memory (ROM; never written)
```

Notice that there are no pipe registers here. This is simply the
architectural state as seen by the programmer. In addition, the
intermediate values computed when executing an instruction are stored in
temporary variables that are not actually part of the state:

```ivy
var fetched : word
var opcode  : opc
var a_val   : word
var take_branch : bool
# ...
```

Notice that these correspond directly to wires in our two-stage
pipeline.  We will see that this correspondence is very useful in
verifying the pipeline.

The values of the temporary variables are computed from the architectural
state by an action `prepare` provided by the ISA:

```ivy
action prepare = {
    fetched := imem(pc);
    opcode  := fetched<<15:13>>;
    ra := fetched<<9:7>>;
    a_val   := rf(ra);
    take_branch := (opcode = 6) & (a_val = 0);
    # ...
}
```

The update of the architectural state is then computed by a second action
`step`:

```ivy
action step = {
    # ... execute / writeback, using a_val, target, ... ...
    if take_branch { pc := target } else { pc := pc + 1 }
}
```

Executing one instruction is the sequence `prepare; step`. The `prepare` action
computes the temporaries from the current architectural state and
`step` consumes them to produce the next state.

The ISA model is passed two parameters, `init_mem` and `init_imem`,
representing the initial contents of data and instruction memory. This
allows us to align it with the arbitrary initial contents of the
hardware memories.

### The trace and the tags

Given the ISA model, we now construct an abstract appliance called
'trace' that builds an execution trace of the ISA to use as a
reference in specifying and verifying the CPU. 

The trace model is a special kind of Ivy object called an 'isolate'.
It is called this because specified properties of the isolate are
verified in isolation, without considering other components of the
system. The trace isolate contains its own instance of the ISA model
called `arch`. It also defines a special type called `tag` to use as
an index into the execution trace.  Values of this type form an
abstract sequence 0, 1, 2, ... We cannot perform arithmetic on these
values, however. The tag type defines only a zero value, a successor
function, and a total order on tags. Using abstract types like `tag`
is an important way that we keep proof obligations decidable for the
SMT solver.

The trace keeps a map `st` from tags to states, where each state
represents both the architectural state and the values of the temporary
variables in that state. 

Here is the essence of the trace model code:

```ivy
var now : tag                 # pointer to the last state
var st(T:tag) : state_t       # the recorded states

after init {
    now := 0;
    arch.prepare;
    st(now) := current;       # gets current arch state as a struct
}

action step = {
    arch.step;                # advance the ISA by one instruction
    arch.prepare;             # compute temporary variables
    now := now.next;          # move to the next tag
    st(now) := current        # record the new architectural state
}
```

The trace model provides an abstract action `step` that executes one instruction
and records the resulting state in the sequence. All the code of the trace
model is in a `specification` section. This means it is ghost code, which is not
translated into hardware. Ivy verifies that it is safe to erase the ghost code
because it can have no side effect on the hardware. 

We now instrument the CPU with more ghost code that keeps track of a
tag for each pipe stage. The tag tells us which instruction in the
trace is currently being executed in that stage. We have a tag `f_tag`
for the F stage and `x_tag` for the X stage. If the `pc` in the F
stage is not shadowed, we call the `trace.step` action to
move forward one instruction. This keeps the trace model in sync with
the CPU:

```ivy
after posedge {
    x_tag := f_tag;                    # X takes what F held
    if ~take_branch {
        f_tag := f_tag.next;           # F advances only if not squashed
        trace.step                     # ... and a new instruction issues
    }
}
```

Notice that the F stage tag only moves forward when `pc` is not shadowed
behind a taken branch.

Here is the big advantage of tagging the pipe stages relative to the
trace.  The correctness of values in each element can be specified by
a single, local invariant, relative to the trace:

```ivy
invariant ~take_branch -> pc = trace.st(f_tag).pc
invariant ir_valid     -> ir = trace.st(x_tag).fetched
invariant rf(R)  = trace.st(x_tag).rf(R)
invariant mem(M) = trace.st(x_tag).mem(M)
```

We have one invariant for the `pc`, one for the instruction pipe
register, one for the register file and one for data memory. Notice
that the `pc` specification is relative to the F stage tag, while the
remaining values are relative to the X stage tag. If we can prove
these simple invariants, we know that the CPU is tracking the
ISA. Though our CPU doesn't have any outputs yet, it will be a simple
matter to show that a sequence of output values produced by the CPU
exactly matches the outputs produced by the ISA model.

Ivy uses an SMT solver to prove the invariants. To do this, Ivy needs
some auxiliary invariants of the trace model. These invariants were
produced by Claude and can be re-used for other implementations of the
same ISA.


## What must be trusted, and what is mechanically checked

For any formal verification approach, it is important to understand
what is trusted. This is especially true in a methodology in which
both the design and the proof are generated by an AI assistant. 
Our Ivy development has several kinds of content, differing in
how much human scrutiny they require and the risks they entail.

**1. The ISA model.** This model is trusted and must be validated by
humans. This is why the model is written in an operational style
that is relatively easy to read and interpret. In principle,
this model also can be compared against other available models or implementations
of the ISA by simulation. An important risk in our pipeline example
is that the specification is too weak, because it does not consider liveness.
That is, we have not specified that the CPU always eventually executes another
instruction. Liveness properties can be specified and proved in Ivy. However, this
highlights a generic risk in formal methods: a specification that is not strong
enough may result in a system with undesired behavior. 

**2. The top-level correctness statement.** If we define outputs
of the CPU and specify their correctness relative to the ISA,
these specifications also must be validated by humans. In a larger
context, these specifications can also be viewed as contracts and validated
against the behavior of other system components.

**3. The CPU implementation.** This is mechanically verified and thus
trust in this code is transferred to trust in the Ivy verification
tool. Most importantly, no trust is placed in the AI agent that
generated the code. Though we are trusting in the correct
translation from Ivy to RTL, we can put a check on this process by
generating a "golden model" in SystemVerilog and using combinational
equivalence checking (for example using Yosys) to ensure that the RTL
that was verified by Ivy is equivalent to the golden model.

**4. The proof scaffolding.** This includes the trace model and any auxiliary invariants used in the
proof, whether produced by humans or AI. These parts of the development are
not trusted and need not be reviewed by humans. A mistake here can result in a
proof failure, but cannot result in a false "verified" result. 

## Generating and checking the proof.

The proof of our simple pipeline is checked by this command:

```bash
$ ivy_check pipe_cpu_ref.ivy
```

This uses an SMT solver and the principle of induction to verify that
the stated invariant properties are in fact always true. This requires
that the invariants be inductive, in the sense that they are true
initially and are preserved by a step of the model (in the hardware
case, a single clock transition). If this isn't true, `ivy_check`
produces a counterexample trace that starts in a state satisfying the
invariants and ends in a state where an invariant is false, showing
that the invariant is not preserved. Getting counterexamples reliably
from the tool is very important when we are trying construct an
inductive invariant. Ivy's restrictions on the use of logical theories
are designed to make the production of correct counterexamples as
reliable as possible.

Finding an inductive invariant that proves a property is challenging.
However, using the reference tagging methodology, we see that the
needed invariants are simple, local, and follow a common pattern. This
makes it a relatively simple matter to generate the invariants using an AI
assistant, as we have done here.

## Scaling the method

The reference tagging approach was probably overkill for verifying our
simple two-stage pipeline. The method shows its value when we extend 
to more complex architectures. As we do this, the trace model can be
reused verbatim, while the tags and invariants scale uniformly. We'll
briefly discuss here a sequence of more elaborate CPU
microarchitectures, moving towards a more realistic machine, and how the
reference tagging approach is applied in these cases. 

### A five-stage pipeline

[This design](https://github.com/kenmcmil/ivy/blob/master/doc/examples/hardware/5stage_cpu_ref.ivy)
is a standard five-stage pipeline with instruction fetch (IF), instruction decode (ID), execution (EX),
memory access (MEM) and write-back (WB) stages. As before, each stage has a tag pointing into the
instruction trace. Stalls in the pipeline affect the advancement of the tags. For example, in case of
a register data hazard, the EX stage is stalled and the tag does not advance. In this design, we begin to
see the advantage of storing the temporary variables in the trace. Each of the pipe registers can be seen
as holding the value of one of the temporary variables in the instruction indicated by its tag. This immediately
gives us the invariant for each pipe register.

### Adding a branch predictor

The previous five-stage pipeline stalls in case of a conditional
branch until the branch condition is resolved in the EX stage. [This
design](https://github.com/kenmcmil/ivy/blob/master/doc/examples/hardware/5stage_bp_cpu_ref.ivy)
avoids stalls by adding a branch predictor. The IF fetches past
unresolved branches by predicting the branch condition.  Instructions
fetched on the wrong path are squashed in the EX stage when the branch
condition is known. The trick to proving this pipeline is that we can
know whether the branch prediction is correct in the IF stage by
consulting the trace, in which the correct branch condition is
recorded. We can then mark the instructions in the pipeline that are
shadowed by mispredictions using ghost variables. Moreover, we step
the trace model only when the fetched instruction in the IF stage is
not shadowed, keeping the CPU and the ISA in sync. For each pipe
register, the invariant only applies when the stage is not
shadowed. We also need the invariant that shadowed instructions never
make it to the MEM or WB stages, which would cause architectural state
to be corrupted.  In this way, the proof of the speculative processor
is only a little more complicated than the proof of the stalling
processor.

The predictor itself doesn't affect the correctness of the CPU, only its performance.
For this reason, we tell Ivy to ignore the branch predictor logic when proving the rest
of the pipeline by putting it in an isolate:

```ivy
isolate bp = {
    wire fetch_pc : addr          # inputs
    wire br_valid : bool
    wire br_pc : addr
    wire br_taken : bool
    wire predicted_taken : bool   # output
    implementation {
        var bht(I:bhtidx) : ctr   # 2-bit saturating counters (bimodal)
        definition predicted_taken = (bht(pred_idx) = 2) | (bht(pred_idx) = 3)
        after posedge { ... nudge bht toward the resolved outcome ... }
    }
}

# in the parent CPU: connect the bp ports
definition bp.fetch_pc = pc
definition bp.br_taken = e_take
definition f_ptaken    = f_is_branch & bp.predicted_taken
```


The branch predictor is a component of the CPU. It declares its inputs
and outputs as wires. These wires are connected appropriately in the
CPU definition. Thus, the branch predictor references nothing in the
CPU directly. 

Because the predictor's logic is in a hidden `implementation` section, Ivy verifies the
CPU with `bp.predicted_taken` left arbitrary; it does not examine the predictor logic.
This kind of information hiding is one of the essential features that Ivy provides
for decomposing large proofs into smaller proofs referencing only local information. 
In principle, we could prove some properties locally in the `bp` isolate, but in this
case there is nothing to prove since CPU correctness does not rely on any properties of `bp`.

### Adding instruction and data cache

[This
design](https://github.com/kenmcmil/ivy/blob/master/doc/examples/hardware/5stage_cache_cpu_ref.ivy)
is a bit tricky because we don't want to pay the overhead of making
the I-cache and the D-cache coherent. Thus, it is not safe to fetch an
instruction from an address after a store to that address. To handle
self-modifying code correctly, we have to change the ISA. We do this
by adding an instruction `FLUSH A` that makes it safe to fetch from a
modified address `A`. The modified ISA model maintains a map `ddirty`
from `addr` to `bool`, indicating the addresses that are currently
unsafe to fetch from. On a fetch from a dirty address, the ISA enters
an error state, setting a Boolean state variable `error`.  The CPU
implements `FLUSH A` by flushing address `A` from both caches in the
MEM stage and by stalling instruction fetch when there is any FLUSH in
the ID through EX stages.

The invariants of the pipeline are only slightly modified to reflect
this. Mainly we have to condition the invariants on having no error in the trace model.
The effect is that the CPU need not continue to execute a program
correctly after the program has gone wrong by unsafely fetching modified code.
Simple invariants are also used to define the content of cache data and main memory
data in terms of the trace model at the MEM stage tag. Changing main memory to a
two-cycle RAM entailed no new invariants.


### Generating the CPU and the proof.

After doing the initial two-stage pipeline exercise, Claude was able to
generate both the CPU designs and the proofs without human assistance
(though the ISA model changes had to be corrected manually). This
included making a plan for incrementally developing and verifying the
design. 

The use of reference tagging in Ivy, including the invariants and the
debugging workflow for the examples above, is described in detail
[here](https://github.com/kenmcmil/ivy/blob/master/doc/examples/hardware/reference_tagging.md).

## From proof to RTLIL

A verified datapath is useful only if it becomes hardware, and this is where the
standard RTL flow resumes. The `ivy_to_rtl` translator emits the design as RTLIL, one module per Ivy
object. Array `var`s become RTLIL memories, wire definitions become cells,
registers become `$dff`s, and `after init` becomes synchronous-reset logic.

Because the output is ordinary RTLIL, we can put a strong check on the
translation process by creating a golden RTL model in SystemVerilog
and using Yosys to verify equivalence of the Ivy-generated RTL with the
golden RTL. In our pipeline example, Claude generated both
the Ivy CPU design and the [golden
model](https://github.com/kenmcmil/ivy/blob/master/doc/examples/hardware/cpu_golden.sv),
as a way of validating the translation. This has the additional
advantage of producing RTL that is readable by engineers not familiar
with Ivy and is usable in SystemVerilog-based tool chains. Both models are
hierarchical and they use identical names for registers and memories,
allowing an efficient combinational equivalence check between
the models.

A Yosys script
[cpu_equiv.ys](https://github.com/kenmcmil/ivy/blob/master/doc/examples/hardware/cpu_equiv.ys)
performs this check:

```bash
$ ivy_to_rtl 5stage_cache_cpu_ref.ivy
$ yosys cpu_equiv.ys
```

The script reads the emitted netlist and the SystemVerilog, flattens both
hierarchies, pairs registers and memories by name with `equiv_make`, expands
memories with `memory_map`, and proves by one-step induction (`equiv_induct`)
that from any equal state the two designs compute the same next state for every
register and memory. Every matched cell is proven, so the generated netlist is
equivalent cycle-per-cycle to an independently written model.

From there the flow is standard. We can synthesize the design using Yosys and simulate it using the golden RTL model with any Verilog simulator. The process of developing the CPU designs using reference tagging is described in detail [here](https://kenmcmil.github.io/ivy/examples/hardware/reference_tagging.html).

## A use model for AI-assisted hardware design with Ivy

Nearly all of the Ivy in these four examples — the datapaths, the
ghost scaffolding, and the local invariants — was generated by Claude,
iterating on the counterexamples that `ivy_check` produces, without human guidance.  The human
effort was concentrated in building the trusted ISA model correctly,
and in providing guidance on the RTL design. A key factor that enabled
this division of labor was the application of the reference tagging
pattern that provided structure to the proof and allowed for efficient
checking of proof with an SMT solver. 

The Ivy repository includes a [Claude
skill](https://github.com/kenmcmil/ivy/blob/master/.claude/skills/reference-tagging/SKILL.md)
that packages the method. It includes a description of the structure
of the Ivy development, including the form and usage of the trace
model, as well as pragmatic information on using Ivy for hardware
design, debugging proofs with Ivy and generating RTL.

## Further reading

- Ivy documentation and tutorials: <https://kenmcmil.github.io/ivy/>
- [Hardware modeling and translation to RTL](https://kenmcmil.github.io/ivy/examples/hardware/basics.html)
- [The pipelined-CPU example](https://kenmcmil.github.io/ivy/examples/hardware/pipe_cpu.html)
- [The reference-tagging method](https://kenmcmil.github.io/ivy/examples/hardware/reference_tagging.html) in full
- [The reference-tagging Claude skill](https://github.com/kenmcmil/ivy/tree/master/.claude/skills/reference-tagging)
- Worked examples:
  [`pipe_cpu_ref.ivy`](https://github.com/kenmcmil/ivy/blob/master/doc/examples/hardware/pipe_cpu_ref.ivy),
  [`5stage_cpu_ref.ivy`](https://github.com/kenmcmil/ivy/blob/master/doc/examples/hardware/5stage_cpu_ref.ivy),
  [`5stage_bp_cpu_ref.ivy`](https://github.com/kenmcmil/ivy/blob/master/doc/examples/hardware/5stage_bp_cpu_ref.ivy),
  [`5stage_cache_cpu_ref.ivy`](https://github.com/kenmcmil/ivy/blob/master/doc/examples/hardware/5stage_cache_cpu_ref.ivy)
