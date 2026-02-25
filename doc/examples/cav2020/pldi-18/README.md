This directory contains examples from the following paper:

Marcelo Taube, Giuliano Losa, Kenneth L. McMillan, Oded Padon, Mooly
Sagiv, Sharon Shoham, James R. Wilcox, Doug Woos: Modularity for
decidability of deductive verification with applications to
distributed systems. PLDI 2018: 662-677

Instructions for verifying, compiling and running these protocols are
found in comments at the ends of the files.


1) toy_consensus.ivy

This is a toy model of a consensus protocol that illustrates the use
of an abstract model and refinement (with indexset.ivy) to keep
verification conditions decidable. This file uses `indexset.vy` as
a representation of finite sets with a majority test.
That file shows how to use tactics to create an abstract data type for
finite sets, and how to use tactics to introduce recursive functions
and apply induction over the natural numbers.


2) Directory multi_paxos

An implementation of a Multi-Paxos consensus protocol using the same
principles. See `multi_paxos/README.md`. 


