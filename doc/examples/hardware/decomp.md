---
layout: page
title: Proof decomposition for pipelines
---

The reference tagging approach is effective for pipelines that keep
just a few instructions in flight. The localized invariants for each
pipeline stage tend to be relatively easy for Ivy to check. However,
when the number of instructions in flight becomes larger, Ivy can have
a hard time generating counterexamples. This is because a true
counterexample requires Z3 to generate a trace with a larger number of
instructions in it.

In order to handle larger CPU designs (for example, a dual-issue
pipeline or an out-of-order processor) we need to break the proof
into parts in a way that both the proofs *and* the counterexamples are
localized. Otherwise, our proofs become hard to debug because we can't
get counterexamples to induction quickly. Here, we will discuss a
proof pattern that allows us to do this. This pattern allows us to
prove the correctness of piplelines in an assume/guarantee style. This
means that the invariants of each pipeline stage are proved *in
isolation*, using only properties of the interfaces between pipeline
stages. Later, we'll see that the same basic decomposition ideas can
be applied in many other situations, for example, out-of-order
processors and cache-coherent multiprocessor designs.

In an assume/guarantee proof, the components are connected by
interfaces that have formally specified protocols. The interface
specifications have ghost state variables that define the abstract
state of the interface, and invariants that determine the
protocol. Usually the interface state contains a tag referring to an
instruction in the abstract ISA trace.  Both the abstract state
variable updates and the invariants also refer to the abstract
trace. This allows us to specify when information crossing the
interface is correct relative to the instruction set architecture.

Each invariant of the interface is a *guarantee* for one side of the
interface (i.e., something to be proved) and an *assumption* for the
other side of the interface. To prove the guarantees of a given
component of the design, Ivy only has to use the assumptions at that
component's interfaces, and not any other components or interfaces
in the design. Because of this, counterexamples only need to refer to
one or two instructions in trace. This additional localization can
greatly improve Ivy's performance in generating counterexamples. This
benefit, however, comes at a cost: we have to structure the proof more
carefully and write a few more invariants to act as the assumptions
and guarantees in the interface specifications.

We will now cover a few basic patterns for defining the system
components, and their interfaces. We'll start with a running example to
help illustrate the patterns.

First example: register file and ALU
------------------------------------

We will start with a very simple three-stage pipeline that executes two
simple instructions on a register file.

The example is in `simple3_dec.ivy`. To keep the focus on the proof
structure, the machine is deliberately tiny. It has an 8-bit word type,
a 2-bit register index type (so four registers) and a 2-bit opcode.
There is no instruction memory and no program counter: one instruction
word arrives each cycle on a primary input `inst_in` and is issued in
order. The only architectural state is a register file `rf`.

An instruction word is laid out as follows:

```
[7:6] op    [5:4] dst    [3:2] s1    ([1:0] unused)
```

There are just two instructions:

  * `op = 1` (ADD1): `rf[dst] := rf[s1] + 1`
  * `op = 0` (NOP):  does nothing (reads and writes no register)

The pipeline has three stages:

  * `rd`  (read):      read the source operand `rf[s1]` and latch it
  * `alu` (execute):   compute `rf[s1] + 1`
  * `wb`  (writeback): write `rf[dst]`

Because `rf` is read in `rd` but not written until `wb`, an instruction
whose source `s1` is the destination of an ADD1 still in `alu` or `wb`
would read a stale value. This is the read-after-write hazard that the
simple-hazard pattern (below) resolves by forwarding the operand back
from `wb` and stalling `rd` while a matching writer is in flight. A NOP
reads no register, so it never stalls.

The trace abstraction
=====================

Unlike our previous pipeline designs that were self-contained, this
design does not read its instructions from a memory, but instead takes
its instructions from a primary input. One way to model this at the
ISA level is to think of the instruction as a nondeterministic choice
that can be driven by the ISA. It is not unusual for an ISA to make
nondeterministic choices. For example, most ISA's can take interrupts
at arbitrary times. The exact point in the instruction stream at which
interrupts are taken is not determined by the ISA model. Instead, it
is determined by details of the hardware implementation. We say the
non-deterministic architectural model is *refined* by the hardware. Refinement
means that every behavior of the hardware corresponds formally to *some*
behavior of the architecture, but not every architectural behavior needs
to be possible in the hardware. To prove refinement, the hardware implementation
provides a *witness* for the nondeterministic choices. This effectively
drives the architectural model's execution in a direction that corresponds to the hardware
execution. We have already seen a small example of this kind of driving: the trace
model determines how many instructions the ISA model executes in each clock cycle.
Now we will use a similar idea to drive the non-deterministic execution sequence.

Our trace model has two changes from the previous examples. First, the
instruction to execute is not fetched from a memory but comes from the
primary input `inst_in`. To keep the ISA model independent of any
particular hardware, the ISA does not refer to this input directly:
its `decode` action takes the instruction word as an *argument*, and
the implementation reads `inst_in` and threads it through `trace.step`
to `arch.decode`. Second, the trace model delays computing the
intermediate values of the instruction until the instruction is known,
that is, until `step` is actually called. Thus, if the current tag is
`t`, then calling `trace.step` first computes the intermediate values
in `trace.st(t)`, then stores the next architectural state in
`trace.st(t.next)`.

Here is the relevant part of the trace model. The `decode` action
computes the intermediate values of the given instruction (its decoded
fields, the operand read `a_val` and the result `res`) against the
current register file, while `writeback` performs the register write.
Keeping them separate lets `step` snapshot the intermediates *before*
the write is applied:

```
action decode(inst : word) = {
    ir  := inst;
    op  := inst<<7:6>>;
    dst := inst<<5:4>>;
    s1  := inst<<3:2>>;
    a_val := rf(s1);
    res   := (a_val + 1 if op = 1 else 0);
}

action writeback = {
    if op = 1 { rf(dst) := res }
}
```

The `step` action takes the instruction word (supplied by the
implementation from `inst_in`), decodes it, records it together with
its freshly computed intermediates as `st(now)`, applies its write,
advances `now`, and snapshots the new current register file:

```
action step(inst : word) = {
    arch.decode(inst);    # compute intermediates for the given instruction
    st(now) := current;   # record the instruction as st(now)
    arch.writeback;       # apply its register write
    now := now.next;
    st(now) := current;   # st(new now) mirrors the updated rf
}
```

Because `decode` is called inside `step`, the intermediate values are
computed only when the instruction is actually issued, and not before.
The implementation supplies the instruction by calling
`trace.step(inst_in)` in the `cpu` isolate. This is what lets us drive
the trace model according to the instructions received at the input of
our design, resolving the nondeterministic choice lazily.

One consequence of this lazy scheme deserves emphasis, because it
shapes the interface invariants below. The state `st(now)` is only a
snapshot of the *current* register file; it does not yet hold a
committed instruction (its intermediates are recomputed on the next
`step`). Only `st(t)` for `t < now` names a genuine executed
instruction. So any instruction still in flight in a pipe register must
carry a tag *strictly* less than `now`. This is exactly why the
`commit_bound` invariant of each interface (below) has the strict form
`valid -> commit < trace.now`, and not merely `commit <= trace.now`.

This scheme allows us to drive the trace model according to
instructions received at the input of our design.

Interface specification pattern for pipelines
---------------------------------------------

In order to isolate the verification of each pipeline stage using
assume/guarantee specifications, we will construct isolates in the Ivy
language following a particular pattern.


Stage isolates
==============

Suppose that 'cpu' is a pipeline with stages x, y and z.  Within cpu,
we will have isolates corresponding to x, y and z.  In our three-stage
pipeline example, the stages are called 'rd' (the read stage), 'alu'
and 'wb' (the write-back stage), and the corresponding isolates are
`rd_stage`, `alu_stage` and `wb_stage`. See, for example, the
definition of `isolate rd_stage` in `simple3_dec.ivy`.

Each of the stage isolates has the following form:

```
implementation {
    isolate y = {

        # state variables
        # ---------------
        register valid : bool
        register r1 : type1
        register r2 : type2
        ...

        # interface wires
        # ---------------
        wire stall_in : bool   # stall signal from next stage
        wire stall_out : bool  # stall signal to previous stage
        wire w1 : wtype1       # input or output
        ...

        # stage logic goes here

        after init {
            valid := false;
            ...
        }

        after posedge {
            if ~stall {
                ...
            }
        }

        ... wire definitions ...

        # auxiliary invariants go here

        specification {
            # ---- tag invariants ---------
            invariant valid -> y_z.commit.succ(x_y.commit)
            invariant ~valid -> y_z.commit = x_y.commit

            # --- other invariants ---------
            invariant [invar1] formula1
            ...
        }                        

    } with cpu, <types>, x_y, y_z
}
 ```

Here <types> are the types whose theories are needed for the
proof. Isolates 'x_y' and 'y_z' are specifications of the interfaces
between stages that that we will discuss below. In our example, these interfaces
between stages are called 'rd_alu', 'alu_wb'. The register 'valid'
indicates that stage 'y' holds a valid instruction (as opposed to a
bubble) in its outgoing pipe register. If the condition
'valid & ~stall_in' holds, the instruction moves forward to the next
stage.

Notice that the stage isolate 'y' is contained in an implementation
section. This means that an isolate that depends on isolate 'cpu' will
not see 'y' unless it explicitly includes 'y' in its 'with'
clause. This allows us to succinctly describe the abstractions needed
to prove all of the specifications using 'with' clauses. For example,
in the `alu` stage of our example, we have interfaces `rd_alu` and
`alu_wb` in the 'with' clause.  This allows the proof of the
invariants of `alu` to use properties of these interfaces as
assumptions.

Also, notice that every stage has some standard invariants that relate
the tags at the interfaces before and after the stage. These are the
same as in the normal reference tagging pattern. They state that the
successive tags differ by one if there is an instruction in the stage
and are the same if there is a bubble.

All wiring between stages is defined in 'cpu'. Thus, an isolate that
declares 'cpu' in its 'with' clause sees all of the definitions of the
inter-stage wires.


Interface isolates
==================

Between a consecutive pair of stages 'x' and 'y', we have an interface specification
isolate 'x_y'. This isolate is completely ghost and serves to specify the assumptions
and guarantees of 'x' and 'y' at the interface. As an example, see the definition of `isolate rd_alu`
in `simple3_dec.ivy`. The general form of the interface isolate is as
follows:

```
private {
    isolate x_y = {
        specification {

        # The tag of the next instruction to cross the interface
        var commit : trace.tag

        # Other ghost state variables of the interface, if any, go here

        after init {
            commit := 0;
        }  

        after posedge {
            if x.valid & ~x.stall_in {
                commit := commit.next
            }
        }

        # Specify guarantees of stage x

        isolate x_props = {
            invariant [commit_bound] commit <= trace.now
                                     & (x.valid -> commit < trace.now)

            # tracking invariants

            invariant [r1_track] x.valid -> x.r1 = trace.st(commit).r1
            ...
        } with cpu, trace, <types>, w_x, x, x_y
                              # w_x is incoming interface of x, if any 

        isolate y_props = {
            # Here, specify any needed properties of x.stall_in and
            # other feedback signals in the pipe

        } with cpu, trace, <types>, x_y, y, y_z
                              # y_z is outgoing interface of y, if any 
    }
}
```

The interface isolate has a ghost state variable 'commit', the tag of
the next instruction to cross the interface. This variable is used to
define the protocol at the interface. Notice that it does not advance
when 'x.stall_in' is true. The tracking invariants thus force stage
'x' to remain at the same instruction in case of a stall.

The invariants of the interface are divided into two groups. Isolates
'x_props' contains guarantees of 'x' (and hence assumptions of
'y'). Similarly, 'y_props' contains guarantees of 'y' (and hence
assumptions of 'x'). Notice that 'x_props' is proved using isolate 'x'
and both its incoming and outgoing interfaces. Similarly, 'y_props' is
proved using 'y' and both its incoming and outgoing interfaces.

In our example, the interface `rd_alu` contains an isolate `rd_props`
representing the guarantees of the `rd` stage (which is `x` in the
pattern) and `alu_props` representing guarantees of the `alu` stage
(which is `y` in the pattern). The guarantees of the earlier stage `x`
generally state correctness of the instruction in the pipe, while the
guarantees of `y` state correctness of forwarding paths from later to
earlier stages. Both of these are tracking invariants that use the
reference tagging pattern.

In the interface `rd_alu`, the tracking invariants `r_dst_track` and
`r_a_track` state the correctness of the decoded instruction and the
latched operand in the pipe register. The tracking invariant
`a_val_track` states the correctness of the `a` operand that is
forwarded from the `wb` stage. We will discuss these invariants in more
detail later.

Notice that the guarantees of stage `x` in the pattern contain a
standard invariant called `commit_bound`. It says that the trace is
always long enough to contain the results of the instruction that is
crossing the interface. As explained above, the strict part of the
bound, `x.valid -> commit < trace.now`, is what makes `st(commit)` a
genuine executed instruction for an in-flight pipe register, given that
the trace computes intermediate values lazily.

Notice that the interface isolate is in a 'private' section so that it
is only used when it is specified explicitly in a 'with' clause.

Top level
=========

The cpu is an isolate with the following structure:

```
isolate cpu = {

    specification {

        # advance the trace, if needed

        after posedge {
            if ~x.stall_in {
                trace.step(inst_in)
            }
        }
    }

    implementation {
        isolate x = { ... } with ...
    }

    private {
        isolate x_y = { ... } with ...

    implementation {
        isolate y = { ... } with ...
    }

    ...
}
```


Handling read-after-write pipeline hazards
------------------------------------------

The most complex question in decomposing the proof of a pipeline is
the handling of pipeline hazards.  We consider first the simple hazard
case where an architectural register 'r' is read in only one stage and
written in only one stage, with the write stage after the read
stage. This situation creates a potential read-after-write hazard,
since a register may be read before a write later in the pipeline has
completed.  A typical example is the register file of a CPU, as in our
simple three-stage example.

In this case, the simplest way to decompose the pipeline into modules
is to put the register file in the writing stage and to pass read commands
through wires from the reading stage to the writing stage, with read results flowing
back from the writing state to the reading stage. The read result wires obey some
typical invariants that we discuss below.

Suppose that in a pipeline, we have a stage 'x' that reads the register file,
a stage 'm' that does something with the register value, and a stage 'w' that writes a result to the
register file. In our example, these stages are `rd`, `alu` and `wb`. 
Say that the 'x' stage reads a
register file 'rf' at address 'a_reg' obtaining value 'a_val'. If
instructions writing 'a_reg' are in the 'm' or 'w' stages, the 'x'
stage stalls because of the read-after-write hazard. 

Now consider the interface 'x_m' between the 'x' and 'm' stages. It
contains the following guarantee for the 'm' stage:

```
isolate m_props = {
    invariant [a_val_track]
        ~x.stall_in -> a_val = trace.st(commit).rf(a_reg)
    with x_props.commit_bound, m_w.w_props.a_val_track
}
```

This says that, if the 'm' stage doesn't stall the 'x' stage, the
register read value has to reflect the updates of all instructions
before the 'commit' tag at the 'x_m' interface. That is, the register
value forwarded from the 'm' to 'x' stages has to be correct at the
interface tag, or we stall. The correctness of the forwarded value at
the `x_m` interface depends combinationally on its correctness at the
`m_w` interface because the stall signal is combinational. This
argument is a bit subtle: if there is no hazard-induced stall, then
the value of the register at that `x_m` tag must be the same as the
value at the `m_w` tag (since the register is not written by the `w`
stage instruction). Thus, correctness of the forwarded value at `m_w`
implies correctness at `x_m`.  The tracking invariant for `a_val` also
depends combinationally on the commit bound. That is, after a new
instruction enters the pipe at the `x_m` interface, we have to know
that the instruction has actually been executed in the trace to show
that the forwarded value matches the value in the trace. These
arguments are a bit tricky, but we don't need to think about them when
writing the proof. We just have to follow the pattern.

In our example, this pattern is in `rd_alu.alu_props`. Notice the
'with' clause of this isolate. Because this is a guarantee of
`alu_stage`, its proof relies on `alu_stage` and also on `alu_wb`,
since this interface contains assumptions of `alu_stage`.  In the
stage decomposition pattern, all proofs depend on just one stage and
the interfaces of that stage.  This is what allows us to simplify
counterexample generation for Z3.

One caveat about the stall signal in the `a_val_track` guarantee. In
the pattern above we wrote `~x.stall_in`, but a guarantee proved in
`m_props` can only mention signals that stage `m` actually controls.
The stall it guards with is therefore not the full stall of `x`, but
the *aggregate* stall that `m` passes back through the `x_m` interface,
reflecting all hazards at `m` and beyond. Our example is too small to
show this clearly: there is only one stage (`alu`) between the reader
and the writer, so the signal happens to be exactly `alu_stall`, and
the tracking invariant `rd_alu.alu_props.a_val_track` uses
`~cpu.alu_stall` rather than `~rd_stall`. (Here `rd_stall` additionally
bundles `rd`'s own local hazard, which is not a downstream forwarding
concern and so does not belong in this guarantee.)

With more stages between `x` and `w`, there would be several hazard
signals to aggregate into `x.stall_in`. The simplest way to handle this
is to *daisy-chain* the stall: at each intermediate interface we
generate a stall signal that reflects all of the hazards later in the
pipe (this interface's own hazard OR the aggregate stall arriving from
the next interface). That aggregate signal is the one we pass back
through the interface, and it is the one used in the tracking invariant
for the forwarded operand at that interface. A future example with a
deeper pipeline will make this concrete; we will add a forward
reference here when it exists.

At the 'm_w' interface, we have:

```
isolate w_props = {
    invariant [a_val_track] a_val = trace.st(commit).rf(a_reg)
    with m_props.commit_bound, w.rf_track
}
```

Here, there is no condition on a stall signal because the 'w' stage
doesn't generate a stall. Notice here, the tracking of 'a_val' depends with
zero delay on tracking of the register file in stage 'w'. This is because 'a_val'
is a combinational signal that depends on 'rf'. We can see this pattern
in our example in `alu_wb.wb_props`. 

The general pattern is that, as we go back in the pipeline from the
writing stage, we move to later instructions. The value read at the
writing stage remains valid as long as there is no hazard. On the
other hand, if there is a hazard, we stall. Thus the 'a_val' tracking
property is preserved as we move back in the pipeline to the reading
stage.

Here is the logic in the 'w' stage isolate dealing with the register file:

```
    after init {
        rf(R) := 0
    }

    after posedge {
        if wb_we {
            rf(d_reg) := a_wb_val
        };
    }
    specification {
        # the register file tracks the committed architectural state
        invariant [rf_track] rf(R) = trace.st(m_w.commit).rf(R)
    }
```

Notice that we don't have to use the commit bound combinationally
here, because we are specifying a register, not a combinational wire.
We can see the above pattern in the `wb_stage` isolate in our example.

This illustrates a general rule of thumb that is worth keeping in mind
when writing the 'with' clauses. Invariants about *combinational wires*
(such as `a_val_track`) usually carry zero-delay dependencies, because
a wire's value is determined in the same cycle by the wires and
registers it is computed from. Invariants about *registers* (such as
`rf_track` and the pipe-register tracking invariants `r_dst_track`,
`r_a_track`, `a_res_track`) usually do not: a register was latched at
the previous posedge from values that already satisfied their
invariants, so its correctness is a unit-delay consequence supplied
automatically by the isolate-level 'with' clause, not something we
assert with zero delay. In particular, `rf_track` depends on the
interface's write-value tracking with *unit* delay (the value was
latched a cycle earlier), so even though `rf` and the forwarded `a_val`
refer to each other, there is no zero-delay cycle to worry about.

Adding write-after-write hazards
--------------------------------

A more complex situation occurs when an architectural register can be
written at multiple stages of the pipeline. A common case of this is
the program counter, which can be incremented in the fetch stage or
updated to a branch target in the execute stage, in case of a
conditional branch. This introduces a potential write-after-write
hazard. In this case we will call the fetch stage the
'early write stage' and the execute stage the 'late write stage'. 
This situation can be complicated by the fact that the condition
for a late write to occur may not be computed until the late-writing
stage. This occurs in the case of a program counter when the branch
condition is not computed until late in the pipeline. 

A simple example with a write-after-write hazard
================================================

The example is in `complex3_dec.ivy`.  As in the simple-hazard example,
one instruction per cycle arrives on the primary input `inst_in`, and
the only architectural state is a single register `r` (one register is
enough to exhibit the hazard).  The instruction word is

```
[7:6] op    [5:0] imm
```

with three instructions:

  * `op = 1` (INC):  `r := r + 1`   -- writes r EARLY, at issue
  * `op = 2` (LOAD): `r := imm`     -- writes r LATE, in the last stage
  * `op = 0` (NOP):  reads and writes nothing

Here, `imm` is an immediate value in the instruction.
The pipeline has three stages: `ew` (early write), `md` (middle), and
`lw` (late write).  The register `r` lives in `ew`.  An INC reads `r`
and performs its write `r := r + 1` at issue, in `ew`; a LOAD's write
`r := imm` happens only when it reaches `lw`, from where the value is
forwarded back to `r` in `ew`.  So `r` is written at two different
stages -- early by INC, late by LOAD -- which is the write-after-write
hazard: while a LOAD is in flight, the `r` held in `ew` is stale until
that LOAD's late write lands.

The middle stage `md` is a plain pass-through; the additional pipeline
delay will allow us to illustrate the full generality of the proof
pattern.

Note that only the INC instruction reads register `r`.  Also note that
the NOP and LOAD instructions read nothing, so they need not stall
behind a pending late write.

A decomposition pattern for write-after-write hazards
=====================================================

To handle the hazard caused by such a case, we will use a strategy in
which writes to the register are forwarded from the late write stage
to the early write stage. At each interface, we maintain ghost state
that remembers whether a write to the register is pending beyond that
stage. In this case, we say the register is 'reserved' at that
interface. When all of the pending writes have completed, the register
is no longer reserved.

### Tracking of architectural registers

A read of a reserved register requires a stall at
the interface if the register is reserved. The tracking invariant
is also modified so that the register only needs to track current tag
when it is not reserved. In other words, the tracking invariant for
register 'r' in early write stage 'x' should look like:

```
invariant [r_track]
    ~(x_y.r_reserved | valid & trace.st(x_y.commit).writes_r)
        -> r = trace.st(w_x.commit).r
```
or, if 'x' is the first stage, `w_x.commit` should be replaced with
'trace.now'.

In our example, the tracking invariant for the architectural register `r` is:

```
invariant [r_track]
    ~(ew_md.r_reserved | valid & trace.st(ew_md.commit).op = 2)
        -> r = trace.st(trace.now).r
```

In other words the condition for executing a late write is that the
instruction opcode is 2 (LOAD). This invariant is found in the `ew` stage,
where the architectural register is implemented. Since this is the
first stage, the commit tag for `r` is `trace.now`.

In the case of a program counter, the reserved flag predicts
whether a pending branch is taken. In the case of our simple example,
the register `r` becomes reserved when a LOAD instruction passes
through the interface.  If there is no late write, then the register
is not reserved and its value is up-to-date.

### Reserved flag invariants

The key invariant maintained by the reserved flags for register 'r' in
stage 'y' is the following:

```
invariant [r_res]
    x_y.r_reserved
        <-> y.valid & trace.st(y_z.commit).writes_r | y_z.r_reserved
```

That is, 'r' is reserved at the incoming interface of 'y' iff 'y'
contains an instruction that writes 'r' late or 'r' is reserved at the
outgoing interface. Here the predicate 'writes_r' indicates that the
instruction in a given trace state writes register 'r'. If 'x' is the
late writing stage, then 'y_z.r_reserved' is by definition false,
since no later stage can write 'r'. 

In our example, this invariant occurs in the middle stage `md` and
relates the `r_reserved` flags at the interfaces `ew_md` and `md_lw`:

```
invariant [r_res]
    ew_md.r_reserved
        <-> valid & trace.st(md_lw.commit).op = 2
```
Because `lw` is the late writing stage, the `r_reserved` flag at
the `md_lw` interface is just `false`.

### Reserved flag updates

The question is how to update the reserved flags at each interface to
maintain this invariant.  If a writing instruction moves forward at
the interface 'x_y', then the flag must be set. On the other hand, if
the flag at the following interface 'y_z' is reset and there is no
writing instruction in stage 'y', then the flag at 'x_y' must be reset.
One way to implement this is using a ghost wire 'y.r_writes_done' that
indicates to 'x_y' that the last write downstream is completing.

Suppose 'w' is the early writing stage and 'z' is the late writing
stage. Then we say an interface 'x_y' is "intermediate" if it is after
'w' and before 'z', but 'y' is not equal to 'z'.  For example, if the
stages are 'w,x,y,z', the 'w_x' and 'x_y' are intermediate, but 'y_z'
is not intermediate, because it is the incoming interface of the late
writing stage 'z'. In our example, the only intermediate interface is
`ew_md`.

The logic for r_reserved in each intermediate interface 'x_y' looks
like this :

```
    var r_reserved : bool
    wire r_writes_done : bool

    after init {
        r_reserved := false;
    }

    after posedge {
        if x.valid & trace.st(commit).writes_r {
            r_reserved := true;
        } else if r_writes_done {
            r_reserved := false;
        }
    }
```


In our example, in interface `ew_md`, the `writes_r` predicate is `op = 2`.

The logic for y.r_writes_done in stage 'y' looks like this:

```
specification {
    definition x_y.r_writes_done =
        y_z.r_writes_done & ~(valid & trace.st(y_z.commit).writes_r)
}
```

However, this occurs only if stage `y` is between two intermediate
interfaces. In our example, there are no such stages. If `y` is the
stage immediately before the late writing stage `z`, then there cannot
be any writes beyond `y_z`. Rather, we consider the writes to complete
at `x_y` when the write pending in stage `y` executes. Thus, we
have:

```
specification {
    definition x_y.r_writes_done =
        valid & trace.st(y_z.commit).writes_r & ~y.stall_in
}
```

In stage `md` in our example, since this stage doesn't stall, we have:
```
specification {
    definition ew_md.r_writes_done =
        valid & trace.st(md_lw.commit).op = 2
}
```

Notice that `r_writes_done` is declared in the interface isolate
`ew_md`, but defined in the stage `md`. This is because it is defined
in terms of the ghost variable `md_lw.commit`, which is visible to
stage `md`, but not to the interface `ew_md`.

### Interface guarantees for write forwarding

At an intermediate interface 'x_y', the 'r_writes_done' condition should satisfy these
guarantees in 'x_y.y_props':

```
invariant [r_we_track] r_z_we -> r_reserved
    with commit_bound, y_z.r_we_track, x_props.r_no_early

invariant [r_wval_track]
    r_writes_done -> r_z_we & r_z_wval = trace.st(commit).r
    with commit_bound, y_z.r_we_track, y_z.r_wval_track,
         x_props.r_no_early
```

where 'y_z' is the interface after 'y', 'r_z_we' is the late write
enable condition for 'r' and 'r_z_wval' is the value written. The
second invariant says that, when all downstream writes to 'r'
complete, the correct final value of 'r' is correctly written. Note
that these invariants depend with zero delay on the corresponding
invariants downstream.

In our example, these invariants are used in `ew_md.md_props`,
substituting `ew` for `x`, `md` for `y` and `lw` for `z`, and adding a
zero-delay dependency on the tracking invariant for the `md` pipe
registers.

At the interface 'y_z', where z is the late writing stage, the guarantees
for the forwarded writes occur in 'y_z.z_props' and look like this:

```
    invariant [r_we_track]
        r_z_we <-> y.valid & ~y.stall_in & trace.st(y_z.commit).writes_r
    with commit_bound, <tracking invariants>
    
    invariant [r_wval_track] r_z_we -> r_z_wval = trace.st(commit).r
    with commit_bound, <tracking invariants>
```

Here, <tracking invariants> is the list of tracking invariants on
which the wires 'r_z_we' and 'r_z_wval' depend combinationally. 

In our example, these invariants appear in `md_lw.lw_props`. 

### Write-after-write invariant

This should be a guarantee in 'x_y.x_props':
```
invariant [r_no_early]
    r_reserved & x.valid -> ~trace.st(x_y.commit).r_early_write 
```
It states that the value of a
late write downstream is not out of date because it is over-written by
an early write. Here, 'early_write' is a predicate that is true of an instruction
that writes 'r' in the early write stage. 

In our example, this invariant is in `ew_md.ew_props` and looks like this:

```
invariant [r_no_early]
    r_reserved & ew_stage.valid -> ~(trace.st(commit).op = 1)
```
Here, '1' is the opcode for INC.

### Read-after-write invariant

If 'x' is the early write stage (that contains register 'r') we also
have to prove this as a guarantee in 'x_y.y_props' to make sure we do not create
a read-after-write hazard:

```
invariant [r_resv_stall] r_x_re & r_reserved -> x.stall_in
    with commit_bound
```

where 'r_x_re' is the early read enable condition for register 'r'
(which may be just 'true').  This says that we have to stall a read of
a reserved register. A similar invariant may be needed
at all of the intermediate interfaces, if stalls propagate backward.

In our example, we have the following in `ew_md.md_props`:

```
invariant [r_resv_stall]
    ew_stage.in_reads_r & r_reserved -> cpu.issue_stall
    with ew_props.commit_bound
```



Conditional write-after-write hazards
=====================================

We now consider applying this decomposition pattern in the case where
the late write is conditional, and the condition is not yet computed
in the early write stage. Typically, this means that the `writes_r`
condition depends on data and that the stall signal is conservative,
in the sense that an instruction in the early write stage is stalled
if later instruct *may* execute a late write.

The example is in `complex3_cmax_dec.ivy`.  It is the same three-stage
pipeline as `complex3_dec.ivy`, with LOAD replaced by CMAX, which rounds
`r` up to its immediate: `CMAX imm` writes `r := imm` exactly when
`r < imm` (its effect is `r := max(r, imm)`).  The essential difference
is that whether the late write occurs now depends on the register value
`r`, not on the opcode alone -- so, unlike a LOAD, a CMAX may or may not
write, and the condition is genuine data that is not available until the
comparison is done in mid-pipe.

In this example, the condition for a late write to occur is captured
in the intermedate value `wl` in the ISA model. The only real change
in the proof, except for adding trackng invariants for new pipeline
registers, is to use this condition as the `writes_r` predicate and to
modify the `in_reads_r` condition so it is true for the CMAX
operation.  The `r_reserved` flag is still true exactly when a write
will occur at a later stage. It now uses information from the trace
model to predict this.  The same comment applies to a program counter
register that is updated at a late stage in case a branch is taken.

Note that this pattern doesn't apply in the case that there is an
early write and a late read of the register. This entails a potential
write-after-read hazard. Because we haven't dealt with this case yet,
the `complex3_cmax_dec` example reads register `r` only in the early
stage.



Five-stage pipeline example
---------------------------

The file '5stage_cpu_dec.ivy' contains an example of these proof
patterns applied to the simple 5-stage pipeline example with no caches
or speculation.

The register file in this example is written only in the write-back
stage 'wb_stage'.  Thus, we use the simple read-after-write hazard pattern. The
architectural register file 'rf' lives in 'wb_stage' and we forward
the two operand reads from the execute stage 'ex_stage' to 'wb_stage'.

Since the pc is written both in the fetch stage 'if_stage' and in
'ex_stage', we use the write-after-write hazard pattern for the pc. The architectural pc
lives in the fetch stage and we forward writes from 'ex_stage' in case
of a taken branch.  The 'pc_writes' condition, indicating a late
write, is exactly 'take_branch' frome the trace model. The only
"intermediate" interface is the 'if_id' interface, between the fecth
and execute stages.

Speculation pattern
-------------------

The late/early write pattern above has the disadvantage that it
requires us to stall any instruction that reads a register that *may* have
is reserved (i.e., has a pending late write) whether the write will
actually occur or not. We can reduce stalls by speculating that the late write
does not occur, allowing instructions that are shadowed behind a late write to proceed in the pipeline and then squashing them
when the late write actually occurs. 







