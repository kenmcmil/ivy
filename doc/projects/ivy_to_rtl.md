Project description
-------------------

In this project, we will add functionality to translate Ivy programs
into hardware RTL in the Yosys RTLIL format.

Ivy extension to synchronous hardware
=====================================

Ivy has ebeen extended to model synchronous hardware with two new features:

1) A new kind of defined symbol called a 'wire'. Like an ordinary
definition, a wire can be a function of state variables and also other
wires. The difference is that the value of a wire is frozen during
execution of an action. Thus, on entry to any exported action, the
value of the wire is equal to its definition. However, as the action
executions, mutations to the variables the wire depends on to not
affect the wire's value. In hardware terms, we can think of the
exported action as representing the update of registers at a clock
edge, with each exported action representing a different clock. The
wires represent combination logic that is assumed to settle before the
clock edge. Like ordinary definitions, wire definitions may not be
cyclic. Thus, we cnnot model combinational cycles.

A wire definition can be in two forms:

```
    wire w : <type>
    definition w = <expr>
```

or

```
    wire w = <expr>
``` 
    
The first form is useful when we wish to hide the definition inside an
isolate. We can declare the wire as part of the isolate's
specification, but put the definition in the implementation, so it is
not externall visible.

2) Given two invariants A,B over the same action interface, we can
specify that we can specify that invariant B has a combinational (or
'zero'delay') dependency on A. This changes the verification
conditions such that, when proving the B holds in the post-state of an
action, we get to assume that A holds in the post-state and not just
the prestate. This feature is useful when we need to assume an
invariant of an isolate (i.e. a hardware module) that has a
combinational pat from input to output. Invariant dependencies may not
be cyclic, as this would be logically unsound. This is an
implementation of "circular compositional reasoning".

Simple examples of compositional proofs of sychronos hardware in Ivy can
be found in `doc/examples/hardware/refinement1.ivy` and `doc/examples/hardware/refinement2.ivy`.


Representing hardware blocks with isolates
==========================================

The hierarchy of the hardware design corresponds to the object
hierarchy in Ivy. That is, if Ivy object `b1` contains sub-objects
`b1.b2` and `b1.b3`, then `b1.b2` and `b1.b3` represent submodules
of `b1` in the elaborated RTL hierarchy.

We do not declare inputs and outputs of the blocks explicitly. Rather,
a wire that is defined in block `b1.b2` and references in `b1.b3` is
implicitly an output of `b1.b2` and an input of `b1.b3`. A wire that
is declared as an `export` is a global (top-level) output, and a wire
declared as an `import` is a global (top-level) input.

The translation of Ivy to RTLIL should maintain the design hierarchy.

Types allowed in Ivy hardware descriptions
==========================================

Wires and state variables in Ivy hardware descriptions can have the following interpreted types:

1) `bool`
2) `bv[k]`  (a bit vector of fixed width `k`)
3) `bv[j] -> bv[k]` (an array with index type `bv[j]` and value type `bv[k]`)

In the RTL, `bool` can be translated to `bv[1]`, but these types are distinct in Ivy.

Interpreted operators on bit vectors in Ivy include:

1) Unsigned arithmetic operators `+`, `-`, `*` and `/`.
2) Bit-field extraction: `bfe[i][j](w)`, representing bits [j:i] of word w.
3) The concatenation operator 'concat'

These types and operators should be translated to corresponding RTLIL cells. Use of other
types in the implementation of hardware blocks should be reported as an error during translation.

Translation from Ivy to RTL
===========================

Translation of an Ivy program to RTL starts with extracting the
implementation code. This stage is similar to what happens in
translation to C++ as implemented in `ivy/ivy_to_cpp.py` for targets
'repl' and 'class'. That is, when selected isolate is compiled to
Ivy's internal representation (class Module) only the implementation
code is kept.

The second stage of the trnslation process is to emit RTLIL. This
involves walking the hierarchy with the user-selected isolate as the
root. The hierarchy is represented by the dictionary mod.hierarchy, in
which every object is mapped to a list of its sub-objects. Each object
in the hierarchy is translated to a hardware module. This involves the
following steps:

1) Find the inputs and outputs of each module. An input of a module A
is a wire that is declaredin A but defined in the parent of
A. Similarly, an output is a wire that is defined in module A and
referenced in the parent of A. An internal wire is neither defined nor
referenced outside the module. For simplicity, Ivy hardware
descriptions must obey the following rules:

a) Every wire declared in a module is either an input, an output, or an
internal wire. 

b) A hardware module cannot refer to a state variable of another module directly.

2) Interconnect wires

Input and output wires need to be ordered in RTL netlists. We derive the
order from the order of declaration of the wires (not their definitions). 

For example, here is some Ivy code:

```
isolate a = {

    import wire inp : bool
    export wire out : bool
    
    isolate b = {
        wire inp : bool
        wire out = f(inp)
    }
    isolate c = {
        wire inp : bool
        wire out = g(inp)
    }

    definition b.inp = inp
    definition tmp = b.out
    definition c.inp = tmp
    definition out = c.out

}

```

This would translate to RTLIL like this:

```
module a
  wire input 1 inp
  wire tmp
  cell b b
      connect inp inp
      connect out tmp
  cell c c
      connect inp tmp
      conect out out
end

module b
   wire input 1 inp
   wire output 2 out
   <cells implementing out = f(inp)>
end

module c
   wire input 1 inp
   wire output 2 out
   <cells implmenting out = g(inp)>
end
```

In the above, in order to implement the definition `c.v = b.w`, we had
to generate an auxiliary wire `tmp` in the top level module `a`. This
wire was used to connect the output `b.out` to the input `c.inp`. Also
notice the inputs and outputs are numbered in order of their declarations.
The top-level inputs are declared with `import wire` while the top-level
outputs are declared with `export wire`. The corresponding wire symbols,
in declaration order, can be found in the lists `mod.input_wires` and
`mod.output_wires`. (Note: these are distinct from `mod.imports` and
`mod.exports`, which hold *action* imports/exports such as the clock.)


A note on symbols in Ivy: A symbol is represented by the immutable class
ivy_logic.Symbol. A symbol `x` has a string name `x.name` and a sort
`x.sort`. The sort corresponds to an Ivy type. Various methods are generating
new symbols. For example `x.prefix(s)` creates a new symbol of the same sort
with string `s` prepended to the name. Symbols are equality comparable and
hashable and are often used as hash table keys. 

3) Convert Ivy actions and wires to RTLIL cells.

In the following discussion, `mod` refers to the current Ivy module, Ivy's internal
representation of an Ivy program (see `ivy/ivy_module.py`). 

a) Expressions

Expressions in Ivy's internal representation are constructd from symbols,
function applications (class `ivy_logic.App`), and a few built-in operators,
including the logical operators (And, Or, Not, Implies, Iff), equality
(Equals) and if-then-else (Ite). A numeric constant is just symbol whose
string name is the decimal or hexadecimal representation of the number.
The bit vecor operators are also just symbols of function sort with string names
such as '+', 'concat', 'bfe[0][1]', etc. To translate an expression into RTLIL,
these operators must be converted to appropriate primitives in RTLIL.

b) Actions

An actions updates state variables, and its execution corresponds to
a clock edge in the hardware design. The set of names of exported actions
is in `mod.public_actions`. The definitions of these actions can be found
indexed by name in the dictionary `mod.actions`. The action definitions are
of class `ivy_actions.Action`.

Each Ivy object may contain of zero or more actions that are
synchronized with a given exported action using a 'mixin' definition
of class `ivy_ast.MixinDef`. A mixin definition `m` associates a local
action `m.mixer()` with an exported definition `m.mixee()`. The mixin definitions
are stored in a defaultdict `mod.mixins` that maps each mixee to
a list of mixin definitions. The mixers in a given ivy object (hardware module) `A` have
names of form `A.x`. This allows use to easily extract all of the state updates associated with
any given block. We must carefully follow these rules to make sure that the RTLIL semantics
mathces the Ivy semantics:

i) An object, action or definition with name `A` has the 'spec'
attribute if the name `A.spec` is defined in `mod.attributes`.

ii) Objects actions and definitions with the 'spec' attribute and all
their decendants are ignored. These are not part of the implementation
logic. They form the specification and its proof.

iii) For each mixee, the mixers from each Ivy object must be executed
in exactly the order that they occur in the list in `mod.mixins`.

iv) It is an error if a mixer in one Ivy object refers to a state
variable updated in another Ivy object. This includes ancestors and
descenands in the object hierarchy. This error must be reported as
interference between the objects.

v) It is an error if any mixin definition that is not ignored is not
of class `ivy_ast.MixinAfterDef`. 

For each object and each exported action, we construct a single action
definition using `ivy_actions.Sequence(*list)` where `list` is the
list of mixer action definitions for that block and that mixee. It is
important that items in `list` occur in the correct order.

c) Action updates

The state variable update associated to an action `act` can be
obtained by calling `act.update(mod)`. This returns a tuple
`(updated,trans,fail)` where `updated` is the set of state variables
that are updated, `trans` is the transition relation and `fail`
describes the failed traces, which we can ignore.  The transition
relation is of class `ivy_logic_utils.Clauses`. This has a field
`defs`, a list of definitions, and `fmlas`, a list of constraints,
which we can ignore.  There is also a field that indexes `defs`,
giving a map from symbols to definitions.  A definition is of class
`ivy_logic.Definition`. It has a field `lhs`, a symbols possibly
applied to some bound variables (class `ivy_logic.Variable`) and a
field `rhs`, an expression that defines the `lhs`. There are
definitions for all of the updated symbols. The value of the symbol
`x` before the action is `__x`. There are also generally many symbols
representing intermediate values whose names also begin with
`__`. These are treated as combinational wires in the RTL. The updated values
of the state variables should be fed into D flip-flops in the RTL.

4) Clock wires

Each expored Ivy action correspond to a clock wire. These clock wires
must be routed as inputs of the hardware blocks, and to the D
flip-flops associated with the corresponding actions.

5) Reset signals

Initializers in Ivy are also mixers, ascociated with the fictional
action named 'init'. These become reset logic in the RTL. We associate
init mixers to Ivy objects in the same way as for the exported actions
and they must obey the same rules.  To implement them in RTL, we have
to route a global reset `rst` signal to all hardware blocks. We
generate the update logic for initializers in the same way as for
eported actions. We then use a multiplexer to select the update value
for each D flip-flop, choosing the initial value if `rst` is true and
the exported action update if it is false.

6) Sub-blocks

For each Ivy object, we create an RTLIL module with a suitable name.
This module is instantiated as a cell in its parant's module. Notice
that different Ivy objects map to a different module inthe RTL, even
if they were originally created as instances of the same Ivy
module. The result is a fully elaborated netlist. 

Ivy to RTL application
======================

The command-line application to translate Ivy to RTLIL is `ivy_to_rtl`
and is implemented in `ivy/ivy_to_rtl.py`. Currently it consists of template
code that simply compiles the Ivy code into a module. The command-line
syntax is:

```
$ ivy_to_rtl <file>.ivy
```

This command should write the entire design into an RTLIL file <file>.il in
the current directory.

