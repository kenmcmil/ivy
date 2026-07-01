# Ivy hardware examples and Ivy-to-RTL translation

These examples exercise Ivy's synchronous-hardware modeling and the
`ivy_to_rtl` translator, which emits a design as a Yosys RTLIL (`.il`)
netlist. See `doc/projects/ivy_to_rtl.md` for the design of the translator.

## Translating a design

```
$ ivy_to_rtl <file>.ivy      # writes <file>.il in the current directory
```

The translator walks the object hierarchy from the design's top module and
emits one RTLIL module per Ivy object. Wires become nets, `wire` definitions
and interpreted operators (`+ - * /`, `bfe`, `concat`, `=`, `if`/`Ite`, the
logical connectives) become RTLIL cells/sigspecs, scalar state variables
become `$dff`s, and each initializer becomes synchronous-reset logic. Array
state variables (type `bv[j] -> bv[k]`, i.e. register files and memories)
become RTLIL memories: reads become asynchronous `$memrd` ports and the
clocked update becomes a `$memwr_v2` port. Each exported action is a clock; a
global `rst` is the reset.

## Examples

| file | what it is |
|------|------------|
| `test_to_rtl.ivy` | one-stage pipeline: registers `inp + 1` (a combinational `inc` submodule feeding a `delay` register). |
| `refinement3.ivy` | a 2-bit counter built by cascading two 1-bit counters `c0`, `c1`; the abstract model `abs` is a specification-only isolate (ignored by the translator). The top module is the global scope. |
| `bfe_concat.ivy` | registers a nibble-swap of the input, `out := old(concat(inp[3:0], inp[7:4]))`, exercising the `bfe` and `concat` operators. |
| `pipe_cpu.ivy` | a two-stage (fetch/execute) pipelined processor with a register file, data memory, and instruction ROM (all array state → RTLIL memories) and a conditional branch resolved in execute (a control hazard). Exposes the PC as `pc_out`. |
| `refinement1.ivy`, `refinement2.ivy` | earlier compositional-proof examples. `refinement3.ivy` is the version written in the intended hierarchical style. |

Each `.il` beside a `.ivy` is the committed golden output of the translator.

## Checking an RTLIL design with Yosys

Structural sanity check of a generated netlist:

```
$ yosys -p "read_rtlil refinement3.il; hierarchy -check -top this; proc; check -assert; flatten; opt"
```

A design with memories (e.g. `pipe_cpu.il`) needs `memory_collect` to gather
the per-port cells into `$mem` cells before `check`:

```
$ yosys -p "read_rtlil pipe_cpu.il; hierarchy -check -top cpu; memory_collect; check -assert"
```

After `opt`, `pipe_cpu` has the expected structure: three memories
(`imem`, `mem`, `rf`), `$sdff`/`$sdffe` registers (Yosys infers the
synchronous reset from the reset multiplexer, and the `ir` enable), `$add`/
`$sub` for the ALU, `$eq` for instruction decode, and `$mux` for the
writeback/branch selects.

## Simulating a design (and loading a memory)

`ivy_to_rtl` translates an array state variable to a memory but does not yet
support initializing it (e.g. loading an instruction ROM from an Ivy `after
init`), so a freshly generated memory reads as all-`x`. To simulate a concrete
program, add a `$meminit_v2` cell for the memory, then run `sim`. For example,
to load a four-instruction program into `pipe_cpu`'s `imem` and zero its
register file:

```
# in module \cpu, before the closing `end`:
  cell $meminit_v2 $meminit$imem
    parameter \MEMID "\\imem"
    parameter \ABITS 8
    parameter \WIDTH 16
    parameter \WORDS 4
    parameter \PRIORITY 0
    connect \ADDR 8'00000000
    connect \DATA 64'<word3><word2><word1><word0>   # low word first (LSBs)
    connect \EN 16'1111111111111111
  end
```

`DATA` is `WORDS * WIDTH` bits, with the word at `ADDR` in the low bits. Then
drive the clock and reset:

```
$ yosys -p "read_rtlil pipe_cpu_prog.il; hierarchy -top cpu; proc; memory_collect;
            sim -clock posedge -reset rst -n 12 -vcd cpu.vcd"
```

With the program `LI r1,5; LI r2,1; SUB r1,r1,r2; BEQZ r0,2`, the `pc_out`
trace after reset is `0, 1, 2, 3, 4, 2, 3, 4, ...`. The `3, 4, 2` shows the
control hazard: the `BEQZ` fetched at PC 3 is resolved a cycle later in the
execute stage, so the instruction already fetched at PC 4 is squashed (a
one-cycle bubble) before the PC redirects to the branch target 2.

## Checking equivalence of two RTLIL designs

`refinement3_ref.il` is a hand-written reference for `refinement3`. It is
*name-matched* to the generated netlist — same module names (`\this`, `\c0`,
`\c1`), instance names, ports, and register wires (`\c0.val`, `\c1.val`) — but
the per-bit combinational logic is written differently: for a 1-bit counter
`val == 1` is just `val` and `val + 1` is `~val`, so the reference uses
`$and`/`$xor` where the generated netlist uses `$eq`/`$add`/`$mux`.

Matching the names of the **state elements and interface** is what lets Yosys
establish the correspondence between the two designs; the internal
combinational wire names need not match.

```
$ yosys -p "
    read_rtlil refinement3.il
    hierarchy -top this; flatten; opt_clean; rename this gate; design -stash gate
    read_rtlil refinement3_ref.il
    hierarchy -top this; flatten; opt_clean; rename this gold; design -stash gold
    design -copy-from gold -as gold gold
    design -copy-from gate -as gate gate
    equiv_make gold gate equiv
    hierarchy -top equiv
    equiv_simple          # combinational: cut at matched registers, SAT each cone
    equiv_status -assert
"
```

`equiv_make` pairs the two designs by name (ports, interconnect wires, and the
flip-flops become `$equiv` points). `equiv_simple` proves each combinational
cone; for sequential designs `equiv_induct` (temporal induction over the
matched registers) can be used instead of / in addition to `equiv_simple`.
Both report `Equivalence successfully proven!` for `refinement3`.

## Checking equivalence against a functional reference

When the two designs do **not** share register names (e.g. comparing against
an abstract model with different state encoding), build a miter and run a
bounded sequential check from the reset state instead:

```
$ yosys -p "
    read_rtlil ref.il;   hierarchy -top top; flatten; rename top gold; design -stash ref
    read_rtlil gen.il;   hierarchy -top top; flatten; rename top gate; design -stash gate
    design -copy-from ref  -as gold gold
    design -copy-from gate -as gate gate
    miter -equiv -make_assert -flatten gold gate miter
    hierarchy -top miter
    sat -seq 10 -prove-asserts -set-init-zero -verify miter
"
```

`-set-init-zero` starts both designs from the reset state (0), which is the
meaningful precondition for hardware with synchronous reset.
