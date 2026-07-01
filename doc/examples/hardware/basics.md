---
layout: page
title: Basics
---

Ivy has special features for designing synchronous hardware. Ivy can
model, specify and verify hierarchical RTL designs. Verified designs
modeled in Ivy can be translated to a the Yosys intermediate language
RTLIL. This makes it possible to simulate a design, check its equivalence
with designs in other langauges, such as SystemVerilog, synthesize it to
a gate level netlist and so forth.

Representing synchronous hardware in Ivy
----------------------------------------

A synchronous hardware design is a collection of *registers* (state that
is updated on a clock edge) connected by *combinational logic* (acyclic
networks of gates that settle between clock edges). In Ivy we model this
with three ingredients:

- ordinary state variables (`var`) for registers,
- a special kind of defined symbol called a *wire* for combinational
  signals, and
- exported actions to represent clock edges, with `after` monitors giving
  the register updates that happen on each edge.

A design is organized as a hierarchy of Ivy objects (isolates), each of
which becomes a module in the generated netlist. The rest of this section
describes each ingredient in turn.

Datatypes for hardware
======================

Wires and state variables in a hardware design may have one of the
following interpreted types:

- `bool`, a single-bit truth value,
- `bv[k]`, a bit vector of fixed width `k`, and
- `bv[j] -> bv[k]`, an array (memory) with a `bv[j]` index and `bv[k]`
  values.

A bit-vector or array type is introduced by declaring an Ivy type and
giving it an interpretation:

    type word
    interpret word -> bv[8]

Note that `bool` and `bv[1]` are *distinct* types in Ivy, even though both
become one-bit signals in the RTL.

The interpreted operators available on bit vectors are:

- the unsigned arithmetic operators `+`, `-`, `*` and `/`,
- bit-field extraction `bfe[i][j](w)`, which selects bits `j` down to `i`
  of `w` (so the result has width `j-i+1`), and
- the concatenation operator `concat`, whose first argument becomes the
  high-order bits of the result.

Arrays are read by application, `mem(a)`, and updated element-wise,
`mem(a) := v`. Using any other type in the implementation of a hardware
block is reported as an error during translation.

Combinational logic
===================

A *wire* is a defined symbol that represents a combinational signal. Like
an ordinary definition, a wire is a function of state variables and of
other wires, and its definition may not be cyclic (we cannot model
combinational loops). A wire may be declared and defined separately,

    wire w : bool
    definition w = <expr>

or in a single combined form,

    wire w = <expr>

The separate form is useful when a wire should be visible in an isolate's
specification but its definition hidden in the implementation.

The inputs and outputs of a block are not declared explicitly. Instead, a
wire that is declared as an `import` is a top-level input of the design,
and a wire declared as an `export` is a top-level output. Here is a purely
combinational block --- a two-input AND gate:

    #lang ivy1.8

    isolate andgate = {
        import wire a : bool
        import wire b : bool
        export wire y : bool
        definition y = a & b
    }

Wires `a` and `b` are top-level inputs and `y` is a top-level output. This
block has no state and no clock; it is just combinational logic.

Clocks, registers and reset states
==================================

Each clock in the design is represented by an *exported action* with no
parameters, called by the environment:

    export action posedge

The execution of the action represents a clock edge. Registers are
ordinary state variables, and their updates on a clock edge are given by
an `after` monitor attached to the clock action. Reset logic is given by
`after init`, which runs when the fictional `init` action fires (the
global reset).

This is where the special semantics of wires matters: during the
execution of an action a wire's value is *frozen* at the value of its
definition on entry to the action. So even though a register update
mutates the state, the wires keep their pre-edge values throughout the
update --- exactly the behavior of combinational logic settling before a
clock edge.

The following non-hierarchical design is an accumulator. It has an input
`x`, an output `sum`, and one register `acc` that adds `x` on every clock:

    #lang ivy1.8
    type word
    interpret word -> bv[8]

    export action posedge

    isolate accum = {
        import wire x : word       # value to add each clock
        export wire sum : word     # the running total (output)
        var acc : word
        after init { acc := 0 }
        after posedge { acc := acc + x }
        definition sum = acc
    }

On reset, `acc` becomes 0; on each clock edge it becomes `acc + x`. The
wire `sum` continuously exposes the register's value as the output.

Hierarchical designs
====================

The hierarchy of a design corresponds to the nesting of Ivy objects: if
object `b` contains sub-objects `b.c` and `b.d`, then `b.c` and `b.d`
become submodules of `b` in the elaborated netlist.

Inputs and outputs of a block are implicit in how its wires are used:

- a wire that is declared in a block but *defined* in its parent is an
  *input* of the block;
- a wire that is defined in a block and *referenced* in its parent is an
  *output* of the block;
- a wire that is neither is *internal*.

To keep this unambiguous, a block must obey two rules: a wire declared in
a block may be assigned only inside the block or by its parent, and a
reference inside a block may only be to the block's own wires or to a wire
of one of its children.

Here is a one-stage pipeline built from two submodules: `inc`, which is
combinational and adds one, and `delay`, which registers its input. The
top module wires them together, `inp -> inc -> delay -> out`:

    #lang ivy1.8
    type word
    interpret word -> bv[8]

    export action posedge

    isolate top = {
        import wire inp : word
        export wire out : word

        isolate inc = {
            wire inp : word
            wire out : word
            definition out = inp + 1
        }
        isolate delay = {
            wire inp : word
            wire out : word
            var val : word
            after init { val := 0; }
            after posedge { val := inp; }
            definition out = val
        }

        definition inc.inp = inp
        definition delay.inp = inc.out
        definition out = delay.out
    }

The definitions at the bottom are the interconnect: `inc.inp` (an input of
`inc`) is driven from the top-level input `inp`, `delay.inp` is driven from
`inc.out` (an output of `inc`), and the top-level output `out` is driven
from `delay.out`. This is `doc/examples/hardware/test_to_rtl.ivy`.

Specifying and verifying synchronous hardware
---------------------------------------------

We can use all of the specification and proof methods available in Ivy for hardware designs.

Specifying and proving invariants
=================================

An *invariant* is a formula that is true in every reachable state. We
attach invariants to an isolate and check them with `ivy_check`. Here two
registers are toggled together and we assert they stay equal:

    #lang ivy1.8

    export action posedge

    isolate sync = {
        var x : bool
        var y : bool
        after init {
            x := false;
            y := false;
        }
        after posedge {
            x := ~x;
            y := ~y;
        }
        invariant x = y
    }

Checking it:

    $ ivy_check sync.ivy
    ...
    OK

Ivy proves the invariant by induction: it holds initially (both registers
are `false`), and if `x = y` before a clock edge then `~x = ~y` after, so
it is preserved.

Using abstract reference models
===============================

A powerful specification technique is to compare a design against an
*abstract reference model*: a simpler design that captures the intended
behavior. The reference model is written as a *specification-only* isolate
--- placed inside a `specification { ... }` block --- so it is used for
proof but is *not* emitted as hardware.

In `doc/examples/hardware/refinement3.ivy`, a two-bit counter is built by
cascading two one-bit counters. The abstract model `abs` is a plain two-bit
counter, and it is specification-only:

    isolate abs = {
        specification {
            wire cout : bool
            var val : uint[2]
            after init {
                val := 0;
            }
            after posedge {
                if en {
                    val := val + 1;
                }
            }
            definition cout = en & (val = 3)
        }
    }

The concrete bit `c0` then states its correctness *relative to* the
reference model --- its carry output should agree with bit 0 of the
abstract counter:

    isolate c0 = {
        wire en : bool
        wire cout : bool
        specification {
            invariant [cout_spec] cout <-> en & (bfe[0][0](abs.val) = 1:uint[1])
        }
        implementation {
            var val : uint[1]
            after init { val := 0; }
            after posedge { if en { val := val + 1; } }
            definition cout = en & (val = 1)
            invariant val = bfe[0][0](abs.val)
        }
    } with this

Because `abs` lives entirely in a `specification` block, the translator
ignores it: only `c0` and `c1` become hardware.

Compositional proofs
====================

The two-bit counter is also a small compositional proof. Each isolate is
verified *separately*, using only the *specifications* (not the
implementations) of the other blocks. The `with this` clause on `c0` and
`c1` says the proof may use the surrounding (abstract) definitions.

Bit `c1` establishes that the design's carry output matches the abstract
carry, but its proof depends on the specification of `c0`:

    isolate c1 = {
        wire en : bool
        wire cout : bool
        specification {
            invariant cout <-> abs.cout with c0.cout_spec
        }
        implementation {
            var val : uint[1]
            after init { val := 0; }
            after posedge { if en { val := val + 1; } }
            definition cout = en & (val = 1)
            invariant val = bfe[1][1](abs.val)
        }
    } with this

The clause `with c0.cout_spec` records that the invariant of `c1` has a
*combinational* (zero-delay) dependency on the invariant `cout_spec` of
`c0`: because the carry chain flows combinationally from `c0` into `c1`,
proving `c1`'s output in the post-state may assume `c0`'s output holds in
the post-state, not just the pre-state. Such dependencies may not be
cyclic. This is Ivy's form of *circular compositional reasoning*, and it
lets each one-bit slice be verified in isolation. The whole proof is
checked with:

    $ ivy_check refinement3.ivy
    ...
    OK

Translating Ivy designs to RTL
------------------------------

The `ivy_to_rtl` command translates an Ivy design to a Yosys RTLIL netlist:

    $ ivy_to_rtl <file>.ivy

This writes the whole elaborated design to `<file>.il` in the current
directory, with one RTLIL module per Ivy object.

Examples
========

**A simple, non-hierarchical design without memories.** Translating the
accumulator above produces a single module. The wire definition and the
`+` become an `$add` cell, the register becomes a `$dff`, and the `after
init` reset value is selected by a `$mux` on the flip-flop's `D` input
(`rst ? 0 : acc + x`):

    $ ivy_to_rtl accum.ivy
    $ cat accum.il
    module \accum
      wire width 8 input 1 \x
      wire width 8 output 2 \sum
      wire input 3 \posedge
      wire input 4 \rst
      wire width 8 \acc
      ...
      cell $add $add$1
        ...
        connect \A \acc
        connect \B \x
        connect \Y $1
      end
      cell $mux $mux$accum.acc
        parameter \WIDTH 8
        connect \A $1
        connect \B 8'00000000
        connect \S \rst
        connect \Y $2
      end
      cell $dff $dff$accum.acc
        parameter \WIDTH 8
        parameter \CLK_POLARITY 1
        connect \CLK \posedge
        connect \D $2
        connect \Q \acc
      end
      connect \sum \acc
    end

Each exported action becomes a clock input, and a global `rst` input is
routed to every block that has state.

**A hierarchical design.** Translating the one-stage pipeline `top` above
produces three modules --- `\top`, `\top.inc` and `\top.delay` --- with
`top` instantiating the two submodules as cells and connecting their
ports, introducing an auxiliary wire where `inc`'s output feeds `delay`'s
input:

    $ ivy_to_rtl test_to_rtl.ivy
    $ cat test_to_rtl.il
    module \top
      wire width 8 input 1 \inp
      wire width 8 output 2 \out
      wire input 3 \posedge
      wire input 4 \rst
      wire width 8 \delay.out
      wire width 8 \inc.out
      cell \top.delay \delay
        connect \inp \inc.out
        connect \out \delay.out
        connect \posedge \posedge
        connect \rst \rst
      end
      cell \top.inc \inc
        connect \inp \inp
        connect \out \inc.out
      end
      connect \out \delay.out
    end
    ...

**Memories and memory initializers.** Array state variables become RTLIL
memories: reads become asynchronous `$memrd` ports and the clocked update
becomes a `$memwr_v2` port. Assignments to an array in `after init` become
power-on memory contents (`$meminit_v2` cells) --- a broadcast fill when a
constant is assigned to the whole array, and one cell per point
assignment. The processor example `pipe_cpu.ivy` uses this to zero its
register file and load a program into its instruction ROM:

    var rf(R:reg) : word          # register file  -> a memory
    var imem(A:addr) : word       # instruction ROM -> a memory
    ...
    after init {
        rf(R) := 0;               # broadcast fill  -> a $meminit covering all words
        imem(0) := 0x6405;        # point write     -> one $meminit cell
        imem(1) := 0x6801;
        ...
    }

Translating it yields memory declarations and initializers:

    $ ivy_to_rtl pipe_cpu.ivy
    $ grep 'memory\|meminit' pipe_cpu.il
      memory width 16 size 256 \imem
      memory width 16 size 256 \mem
      memory width 16 size 8 \rf
      cell $meminit_v2 $meminit$imem$21
        ...
        connect \ADDR 8'00000000
        connect \DATA 16'0110010000000101      # 0x6405
      ...

See [the pipelined CPU example](pipe_cpu.html) for the full design.

Equivalence checking
====================

Because the translated design is an ordinary RTLIL netlist, Yosys can check
it for equivalence against a design written in another language, such as
SystemVerilog. Here is the combinational nibble-swap written in Ivy,

    #lang ivy1.8
    type byte
    interpret byte -> bv[8]
    type nibble
    interpret nibble -> bv[4]

    isolate swap = {
        import wire inp : byte
        export wire out : byte
        wire lo : nibble
        wire hi : nibble
        definition lo = bfe[0][3](inp)
        definition hi = bfe[4][7](inp)
        definition out = concat(lo, hi)
    }

and in SystemVerilog:

    module swap(input [7:0] inp, output [7:0] out);
      assign out = {inp[3:0], inp[7:4]};
    endmodule

We translate the Ivy design, then have Yosys pair the two by port name and
prove each output cone equivalent with `equiv_simple`:

    $ ivy_to_rtl swap.ivy
    $ yosys -p "
        read_verilog -sv swap.sv
        hierarchy -top swap; rename swap gold; design -stash gold
        read_rtlil swap.il
        hierarchy -top swap; rename swap gate; design -stash gate
        design -copy-from gold -as gold gold
        design -copy-from gate -as gate gate
        equiv_make gold gate equiv
        hierarchy -top equiv
        equiv_simple
        equiv_status -assert
    "
    ...
    Equivalence successfully proven!

For a design with registers, matching the *state-element* names lets
`equiv_make` establish the correspondence, and `equiv_induct` (temporal
induction over the matched registers) proves sequential equivalence. See
`README.md` in this directory for that recipe.

Simulation
==========

A translated design can be simulated with Yosys's `sim` command to produce
a `.vcd` waveform trace. Since `pipe_cpu.ivy` loads its own program in
`after init`, the generated netlist is self-contained:

    $ ivy_to_rtl pipe_cpu.ivy
    $ yosys -p "read_rtlil pipe_cpu.il; hierarchy -top cpu; proc; memory_collect;
                sim -clock posedge -reset rst -n 12 -vcd cpu.vcd"

Inspecting the `pc_out` output in `cpu.vcd`, the program-counter trace
after reset is `0, 1, 2, 3, 4, 2, 3, 4, ...`: the processor fetches
sequentially and then loops back to the branch target 2. See [the
pipelined CPU example](pipe_cpu.html) for the details.

Synthesis
=========

Finally, the netlist can be synthesized to a gate-level implementation.
Here we synthesize the accumulator/pipeline example to a small set of
generic gates plus flip-flops:

    $ ivy_to_rtl test_to_rtl.ivy
    $ yosys -p "read_rtlil test_to_rtl.il; synth -top top -flatten;
                abc -g AND,OR,XOR; opt_clean; stat"
    ...
      6   $_AND_
      1   $_NOT_
      7   $_XOR_
      8   $_SDFF_PP0_

The eight-bit incrementer becomes AND/XOR/NOT gates feeding eight
synchronous-reset flip-flops. To map to a real standard-cell library
instead of generic gates, pass a Liberty file to `abc` with
`abc -liberty <cells>.lib` (and `dfflibmap -liberty <cells>.lib` for the
flip-flops).
