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
logical connectives) become RTLIL cells/sigspecs, state variables become
`$dff`s, and each initializer becomes synchronous-reset logic. Each exported
action is a clock; a global `rst` is the reset.

## Examples

| file | what it is |
|------|------------|
| `test_to_rtl.ivy` | one-stage pipeline: registers `inp + 1` (a combinational `inc` submodule feeding a `delay` register). |
| `refinement3.ivy` | a 2-bit counter built by cascading two 1-bit counters `c0`, `c1`; the abstract model `abs` is a specification-only isolate (ignored by the translator). The top module is the global scope. |
| `bfe_concat.ivy` | registers a nibble-swap of the input, `out := old(concat(inp[3:0], inp[7:4]))`, exercising the `bfe` and `concat` operators. |
| `refinement1.ivy`, `refinement2.ivy` | earlier compositional-proof examples. `refinement3.ivy` is the version written in the intended hierarchical style. |

Each `.il` beside a `.ivy` is the committed golden output of the translator.

## Checking an RTLIL design with Yosys

Structural sanity check of a generated netlist:

```
$ yosys -p "read_rtlil refinement3.il; hierarchy -check -top this; proc; check -assert; flatten; opt"
```

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
