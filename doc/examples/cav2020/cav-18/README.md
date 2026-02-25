This directory contains examples from the following paper,
decomstrating eager abstraction:

Kenneth L. McMillan: Eager Abstraction for Symbolic Model
Checking. CAV (1) 2018: 191-208

The files of the form *_inv.ivy use invariarant checking, while the
corresponding files of the form *_mc.ivy use eager abstraction and
model checking.

The examples are:

1) german: toy cache coherence protocol
2) flash: model of real chache coherence protocol
3) tomasulo: model of out-of-order execution unit
4) vs_paxos: virtually synchronous Paxos

All the examples can be checked with this command:

    $ ivy_check <file>.ivy


