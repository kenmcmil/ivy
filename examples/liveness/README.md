This directory contains selected examples of proving liveness
properties from these papers:

Oded Padon, Jochen Hoenicke, Giuliano Losa, Andreas Podelski, Mooly
Sagiv, and Sharon Shoham: Reducing Liveness to Safety in First-Order
Logic. POPL 2018: Article 26.

Oded Padon, Jochen Hoenicke, Kenneth L. McMillan, Andreas Podelski,
Mooly Sagiv, Sharon Shoham: Temporal Prophecy for Proving Temporal
Properties of Infinite-State Systems. FMCAD 2018: 1-11

Oded Padon, Jochen Hoenicke, Kenneth L. McMillan, Andreas Podelski,
Mooly Sagiv, Sharon Shoham: Temporal Prophecy for Proving Temporal
Properties of Infinite-State Systems. FMSD 2021. Forthcoming.


The examples are:

1) ticket.ivy: running example of the POPL'18 paper
2) ticket_nested.ivy: running example of the FMCAD'18 paper that requires temporal prophecy
3) alternating_bit_protocol.ivy: alternating bit protocol example from the FMCAD'18 and FMSD'21 papers
4) hybrid_reliable_broadcast_cisa.ivy: hybrid reliable broadcast example from the FMCAD'18 and FMSD'21 papers
5) tlb.ivy: TLB shootdown example from the FMCAD'18 and FMSD'21 papers


All the examples can be checked with this command:

    $ ivy_check <file>.ivy
