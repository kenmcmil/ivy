---
layout: page
title: IVy command reference
---

IVy's commands share a common argument syntax:

*command* *option*=*value* ... *file*.ivy

or

ivy *verb* *option*=*value* ... *file*.ivy

Common options
--------------

These options are common to all the IVy commands. In the following,
`name` represents a hierarchical IVy name, which may contain the `.`
character, and `boolean` represents a Boolean value `true` or `false`.


`isolate=name`

This options specifies the name of a isolate to verify or extract. 

`show_compiled=boolean`

If true, this option causes a representation of the elaborated IVy
code to be printed before doing any other work. The elaborated code
reflects all the module instantiations as well as the various
transformations performed by IVy's compiler to produce an
isolate. This is useful to see in detail what is contained in an
isolate.

`pedantic=boolean`

If true, certain optional warnings are enabled. The default value is false.

`track=string`

The string is a semicolon-seprated list of expressions, or the name of
a file ending in `.trk` that contains the list. When displaying a
counterexample, changes to the values of these expressions are
tracked. Without this option, all symbols are tracked.


Commands
--------

`ivy_check`
==========

[Alternately: `ivy check`]

This command checks the proof of an IVy program. This includes
checking all the invariants and program assertions as well as the
non-interference check which guarantees that the division of the proof
into isolates is sound. If a particular isolate is specified with the
`isolate` option, then only the guarantees of this isolate are
checked.  To guarantee correctness of the program, it must be checked
without the `isolate` option.

During checking, `ivy_check` prints a summary of the contents of each
isolate being verified, including all assumptions and guarantees. For
each check of a guarantee, `PASS` is printed if the check passes and
`FAIL` if it fails.

The options of the `ivy_check` command are:

`diagnose=boolean`

If true, this options causes the check to stop at the first guarantee
that fails. A counterexample for this guarantee is constructed and the
graphical counterexample viewer is launched to display the
counterexample. The default value is false.

`trace=boolean`

If true, this options causes the check to stop at the first guarantee
that fails. A counterexample for this guarantee is constructed and a
corresponding execution trace is printed on standard out. The trace is
formatted so that in an emacs compilation buffer, references to source
lines are active links. The printed trace can be more convenient than the
graphical counterexample viewer, especially if the state contains functions
or relations of arity greater than two. The `track` option (see above) is
often useful with `trace` for debugging purposes. 
The default value is false.

`out=file.a2g`

With `trace=true` this causes the counterexmple trace to written to
the file `file.a2g`.  The trace is in a binary format and can be
viewed with `ivy replay` or `ivy interact`.  Without this option, the
trace is printed in a readable format on standard out.

`summary=boolean`

If true, this causes the summary to be printed, but no actual checking
occurs. The default value is false.

`mutax=boolean`

If true, the check on use of mutable symbols in axioms is
relaxed. This feature should be used with caution. In principle an
axiom should be a tautology, in which case it is safe to assert it
even if it contains mutable symbols. In practice, however, it is very
easy to rule out possible system behaviors by incorrect use of axioms.
The default value of this option is false.

`interference=boolean`

If false, the interference check is not applied. This feature is
unsound and should be applied only as a temporary measure. The default
value is true.

`complete=logic`

This option affects the behavior of the fragment checker that checkers
whether verification conditions are contained in the prover's
decidable fragment. The possible values of `logic` are: 

- `epr` This is the "effectively propositional" fragment, which is extended to
  include stratified use of function symbols.
- `fo` This is unrestricted first-order logic modulo the prover's theories.

The last option does not guarantee decidability and may result in
significant instability of the prover. The default value is `epr`.

`macro_finder=boolean`

This option enables the "macro finder" option in Z3. This detects
quantified formulas that behave as macros, and eliminates them by
substitution. This option is usually helpful, but occasionally causes
Z3 to be very slow. The default is true.

`incremental=boolean`

If true, Z3 is used incrementally when checking invariants. Default is true.

`seed=integer`

Sets the random seed for the SMT solver. 

`check=pattern,...,pattern`

Restricts the checks that are performed to those whose name matches one
of the given patterns. A check's name is the name of the invariant,
property or program assertion, including its enclosing object/isolate
prefix (the name printed in the summary, for example `cpu.invar12` or
`index.spec.transitivity`). A check is performed if any pattern occurs
somewhere in its name (a substring match, so a pattern need not match the
whole name). In a pattern, all characters are matched literally except:

- `.` matches a literal dot, so it can be used to delimit name
  components (for example `cpu.` matches the components of `cpu`, such as
  `cpu.invar12`, but not `cpufoo`);
- `?` matches any single character.

Checks that are not selected are still *assumed* (they remain part of the
inductive hypothesis); they are simply not verified. This is useful for
focusing on a single failing invariant while debugging. Unnamed program
assertions are never selected when this option is given. The default is
empty, which selects all checks.

For example, `check=cpu.` checks only the components of object `cpu`, and
`check=invar12,invar15` checks only those two invariants.

`assert=file:line`

Restricts checking to the single invariant, property or program
assertion at the given source line of the given file (the `.ivy`
extension of the file name is optional). Like `check=`, unselected checks
are still assumed. This option predates, and is subsumed by, `check=`;
the two filters are conjoined if both are given.

`ivy replay`
===========

Prints out a readable version of a trace stored with `out=file.a2g`. The
filename must end with `.a2g`. The `track` option (see above) is useful
for controlling the output. 

ivy_show
========

This command prints the elaborated program (see the option
`show_compiled` above) and exits.


`ivy interact`
==============

This command runs an interactive user interface for constructing
inductive invariants. The file argument of this command can be either
an Ivy file (`.ivy`) or a trace file (`.a2g`). The latter is useful
for debugging a counterexample trace using the graphical interface,
and allows refining an invariant to eliminate a counterexample to
induction previously produced.

The options are as follows:

`ui=interface`

Here, `interface` specifies the user interface for invariant construction. The values are:

- `art` This interface supports interactive construct of an Abstract Reachability Tree.
- `cti` This interface supports an interactive approach to invariant construction based
   on counterexamples to induction.

The default value is `art`.

ivyc
----

This command compiles an Ivy program to executable code. The `isolate` option
can be used to compile code for a single isolate. 

The options are:

`target={repl,test,class}"

The `ivyc` command can extract code in several forms:

- `repl` This is a "read-eval-print" loop that reads calls to exported actions from the
standard input and writes standard output on calls to imported actions. Each process
in the Ivy program is compiled to a separate executable. 

- `test` This composes the program with an automatically generated randomized tester to form a single executable.

- `class` This produces only a C++ class, without a main function, and does not produce an executable.

The default is `repl`.

`classname=cname`

With `target=class`, this gives the name of the extracted C++
class. The default is the name of the main IVy file, without the
`.ivy` extension. The names of the extracted header and implementation
files are `cname.h` and `cname.cpp` respectively.

`build=boolean`

If false, C++ code is extracted, but not compiled. Default is true.

`main=cname`

Determines the name of the main function, if one is generated. The default is `main`.

`outdir=directory`

Causes output files to be generated in `directory`. Default is the current directory.

 
 

 
