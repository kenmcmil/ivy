This directory contains resources to aid in evaluating the artifact.
The paper does contain performance figures for Ivy. We have, however,
attempted to provide examples here demonstrating all of the
functionality and applications of Ivy that are discussed in the paper.

Documentation
=============

Documentation on Ivy can be found at this URL:

http://microsoft.github.io/ivy/

For a quick start, see the section headed "Ivy by Example". The
section headed "Documentaiton" provides an overview of Ivy, covering
the language, the command-line tools, the decidable fragment and the
logical framework.

The examples referred to in the documentation can be found in the
directory `~/ivy/doc/examples`. The source code can be found in
`~/ivy/ivy`.

Editor support
==============

We recommend using the emacs editor to view and edit Ivy files, as it
provides syntax highlighting and automatic indentation. Also, it is
convenient to run Ivy in an emacs compilation buffer, since this
allows you to click on messages to go directly to the cited line in
the source code.  From a source buffer, use `Meta-x compile` and then
enter an Ivy command such as `ivy_check file.ivy` in place of the
default command `make`. Use `Meta-x recom` to run the command again.

Examples from the paper
=======================

In this directory you will find examples demonstrating the various
features of the tool. Each example source file contains instructions
for running the example.

1) modular.ivy

This example is used in the paper to demonstrate a number of language
features, including modularity and theory hiding.

2) modular_mc.ivy

The same example, but verified using model checking and eager abstraction
rather than invariant checking.

3) liveness.ivy

A simple example demonstrating proof of a liveness property using the
liveness-to-saftey transformation.

4) tactic.ivy

A simple example demonstrating the use logical tactics to keep the
verification conditions decidable.

5) borrow.ivy

A simple example showing the compiler's use of borrowing to allow
modifying a map in place. This example demonsrates the V2 compiler,
which is written in Ivy and capable of compiling itself.

Tutorial examples
=================

These tutorial examples are included here in order to illustrate
specific features of Ivy described in the paper. Various other
examples may be found in the online Ivy documentation.

1) `leader_tutorial*.ivy`

A simple parameterized leader election protocol, including an abstract
model and implementation. See the file `leader_tutorial.md` for
a detailed discussion of this file.

2) `token_ring.ivy`

An example showing compositional testing of distributed lock server
using a token ring. including isolated testing of protocol layers.

3) `german_bmc_bug.ivy` and `german_mc_bug.ivy`

Examples showing discovery of a bug by either bounded model checking
or underapproximate finite-state model checking (the BMC example takes
a few minutes on the VM).

4) `natural_deduction.ivy`

A collection of small theorems proved by natural deduction.

Examples from research cited papers
===================================

See the README.md files in the various directories for more
information.

1) Directory pldi-18

This contains examples of using modularity for decidability from this
paper.

Marcelo Taube, Giuliano Losa, Kenneth L. McMillan, Oded Padon, Mooly
Sagiv, Sharon Shoham, James R. Wilcox, Doug Woos: Modularity for
decidability of deductive verification with applications to
distributed systems. PLDI 2018: 662-677

The examples are included to support claims in the paper regarding
modularity and decidability, and also illustrate more involved use of
logical tactics.

2) Directory cav-18

This contains examples using eager abstraction and model checking
from the following paper:

Kenneth L. McMillan: Eager Abstraction for Symbolic Model
Checking. CAV (1) 2018: 191-208

3) Directory sigcomm-19

This directory contains an example of using Ivy to specify and test
implementations of QUIC, a complex Internet Protocol, from the
following paper:

Kenneth L. McMillan, Lenore D. Zuck: Formal specification and testing
of QUIC. SIGCOMM 2019: 227-240

An example of one open-source implementation of QUIC called picoquic is
included in the artifact. Instructions for testing picoquic can be found
in the file sigcomm-19/README.md.

4) Directory liveness

This directory contains selected examples of proving liveness
properties from these papers:

Oded Padon, Jochen Hoenicke, Giuliano Losa, Andreas Podelski, Mooly
Sagiv, and Sharon Shoham: Reducing Liveness to Safety in First-Order
Logic. POPL 2018: Article 26.

Oded Padon, Jochen Hoenicke, Kenneth L. McMillan, Andreas Podelski,
Mooly Sagiv, Sharon Shoham: Temporal Prophecy for Proving Temporal
Properties of Infinite-State Systems. FMCAD 2018: 1-11
