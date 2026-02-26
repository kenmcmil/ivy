This directory contains an example implementation of the Multi-Paxos
consensus protocol. Files of interest are:

1) multi_paxos_system.ivy: the main file
2) multi_paxos_protocol.ivy: abstract protocol mode, used in proof
3) nodes.ivy: node datatype including node sets with majority
4) network_shim_tcp.ivy: implements broadcast over TCP

To verify the implementation, use this command (this may take a while
on the VM, but should eventually succeed):

    $ ivy_check multi_paxos_system.ivy

Assuming this is successful, you can compile the code like this:

    $ ivyc multi_paxos_system.ivy

Now you can run some servers just as in the `toy_consensus` example.
We create process per node in separate terminals. We need at least two
processes, so let's create terminal A and terminal B and do the following:

    A: $ ./multi_paxos_system 2 0
    A: >
    B: $ ./multi_paxos_system 2 1
    B: >

This creates node 0 and node 1 in a network where `max` is 2 (so there are three
possible nodes altogether). In the run shown below, a quorum is established at round 8,
with node 0 (in terminal A) as leader. We can as node 0 to propose a value by entering this in terminal A:

    A: > system.server.propose(0)
    A: = 1   

The server returns 1 (true) meaning that the value was proposed. After some deliberation, the two servers
reacha a decision and output:

    A: < system.server.decide(0,"0")
    B: < system.server.decide(0,"0")

We ask node 0 to propose 42, and get this:

    A: > system.server.propose(42)
    A: = 1   
    A: < system.server.decide(1,"42")
    B: < system.server.decide(1,"42")

Now we enter ^C in terminal A, to kill node 0, and restart it.

    A: ^C
    B: EOF ON SOCKET
    A: $ ./multi_paxos_system 2 0 # if this results in a "bind failed: Address already in use" error, wait a few seconds and try again

Now (in this particular run) the servers establish a quorum again at round 15.
This time node 1 is the leader. If we ask node 0 to propose a value, it fails:

    A: > system.server.propose(7)
    A: = 0

We ask node 1 to propose a value:

    B: > system.server.propose(7)
    B: = 1
    A: < system.server.decide(2,"7")
    A: < system.server.decide(0,"0")
    A: < system.server.decide(1,"42")
    B: < system.server.decide(2,"7")

Notice that after restarting, node 0 has recovered the decisions made
previously.

Below is the full transcript of this interaction, including the debugging messages
that show what messages were sent. Of course, Multi-Paxos is not intended to be used
from a terminal in this way. Rather, it is meant to be a library that provides as service.
To compile it as a C++ class rather than a REPL, use this command:

    $ ivyc target=class multi_paxos_system.ivy

This creates a header file multi_paxos_system.h and an implementation file multi_paxos_system.cpp.
These can be linked with application code. For example the above-cited paper, the libarary was
linked with a simple key/value store application written in C++ for testing in the AWS cloud.
That application is not included in this demo.


Terminal A:
-----------

    $ ./multi_paxos_system 2 0
    > binding id: 0 port: 5990
    < shim.debug_sending(0,{m_kind:one_a,m_round:2,m_inst:0,m_node:0,m_value:"",m_votemap:{offset:0,elems:[]}})
    < shim.debug_sending(1,{m_kind:one_a,m_round:2,m_inst:0,m_node:0,m_value:"",m_votemap:{offset:0,elems:[]}})
    < shim.debug_sending(0,{m_kind:one_a,m_round:4,m_inst:0,m_node:0,m_value:"",m_votemap:{offset:0,elems:[]}})
    < shim.debug_sending(1,{m_kind:one_a,m_round:4,m_inst:0,m_node:0,m_value:"",m_votemap:{offset:0,elems:[]}})
    < shim.debug_receiving({m_kind:one_a,m_round:4,m_inst:0,m_node:0,m_value:"",m_votemap:{offset:0,elems:[]}})
    < shim.debug_sending(0,{m_kind:one_a,m_round:6,m_inst:0,m_node:0,m_value:"",m_votemap:{offset:0,elems:[]}})
    < shim.debug_sending(1,{m_kind:one_a,m_round:6,m_inst:0,m_node:0,m_value:"",m_votemap:{offset:0,elems:[]}})
    < shim.debug_receiving({m_kind:one_a,m_round:6,m_inst:0,m_node:0,m_value:"",m_votemap:{offset:0,elems:[]}})
    < shim.debug_receiving({m_kind:one_a,m_round:3,m_inst:0,m_node:1,m_value:"",m_votemap:{offset:0,elems:[]}})
    < shim.debug_sending(0,{m_kind:one_a,m_round:8,m_inst:0,m_node:0,m_value:"",m_votemap:{offset:0,elems:[]}})
    < shim.debug_sending(1,{m_kind:one_a,m_round:8,m_inst:0,m_node:0,m_value:"",m_votemap:{offset:0,elems:[]}})
    < shim.debug_receiving({m_kind:one_a,m_round:8,m_inst:0,m_node:0,m_value:"",m_votemap:{offset:0,elems:[]}})
    < shim.debug_receiving({m_kind:one_b,m_round:8,m_inst:0,m_node:1,m_value:"",m_votemap:{offset:0,elems:[]}})
    system.server.propose(0)
    < shim.debug_sending(0,{m_kind:two_a,m_round:8,m_inst:0,m_node:0,m_value:"0",m_votemap:{offset:0,elems:[]}})
    < shim.debug_sending(1,{m_kind:two_a,m_round:8,m_inst:0,m_node:0,m_value:"0",m_votemap:{offset:0,elems:[]}})
    < shim.debug_sending(0,{m_kind:two_b,m_round:8,m_inst:0,m_node:0,m_value:"0",m_votemap:{offset:0,elems:[]}})
    = 1
    > < shim.debug_receiving({m_kind:two_a,m_round:8,m_inst:0,m_node:0,m_value:"0",m_votemap:{offset:0,elems:[]}})
    < shim.debug_sending(0,{m_kind:two_b,m_round:8,m_inst:0,m_node:0,m_value:"0",m_votemap:{offset:0,elems:[]}})
    < shim.debug_receiving({m_kind:two_b,m_round:8,m_inst:0,m_node:0,m_value:"0",m_votemap:{offset:0,elems:[]}})
    < shim.debug_receiving({m_kind:two_b,m_round:8,m_inst:0,m_node:0,m_value:"0",m_votemap:{offset:0,elems:[]}})
    < shim.debug_receiving({m_kind:two_b,m_round:8,m_inst:0,m_node:1,m_value:"0",m_votemap:{offset:0,elems:[]}})
    < shim.debug_sending(0,{m_kind:decide,m_round:8,m_inst:0,m_node:0,m_value:"0",m_votemap:{offset:0,elems:[]}})
    < shim.debug_sending(1,{m_kind:decide,m_round:8,m_inst:0,m_node:0,m_value:"0",m_votemap:{offset:0,elems:[]}})
    < system.server.decide(0,"0")
    < shim.debug_receiving({m_kind:decide,m_round:8,m_inst:0,m_node:0,m_value:"0",m_votemap:{offset:0,elems:[]}})
    system.server.propose(42)
    < shim.debug_sending(0,{m_kind:two_a,m_round:8,m_inst:1,m_node:0,m_value:"42",m_votemap:{offset:0,elems:[]}})
    < shim.debug_sending(1,{m_kind:two_a,m_round:8,m_inst:1,m_node:0,m_value:"42",m_votemap:{offset:0,elems:[]}})
    < shim.debug_sending(0,{m_kind:two_b,m_round:8,m_inst:1,m_node:0,m_value:"42",m_votemap:{offset:0,elems:[]}})
    = 1
    > < shim.debug_receiving({m_kind:two_a,m_round:8,m_inst:1,m_node:0,m_value:"42",m_votemap:{offset:0,elems:[]}})
    < shim.debug_sending(0,{m_kind:two_b,m_round:8,m_inst:1,m_node:0,m_value:"42",m_votemap:{offset:0,elems:[]}})
    < shim.debug_receiving({m_kind:two_b,m_round:8,m_inst:1,m_node:0,m_value:"42",m_votemap:{offset:0,elems:[]}})
    < shim.debug_receiving({m_kind:two_b,m_round:8,m_inst:1,m_node:0,m_value:"42",m_votemap:{offset:0,elems:[]}})
    < shim.debug_receiving({m_kind:two_b,m_round:8,m_inst:1,m_node:1,m_value:"42",m_votemap:{offset:0,elems:[]}})
    < shim.debug_sending(0,{m_kind:decide,m_round:8,m_inst:1,m_node:0,m_value:"42",m_votemap:{offset:0,elems:[]}})
    < shim.debug_sending(1,{m_kind:decide,m_round:8,m_inst:1,m_node:0,m_value:"42",m_votemap:{offset:0,elems:[]}})
    < system.server.decide(1,"42")
    < shim.debug_receiving({m_kind:decide,m_round:8,m_inst:1,m_node:0,m_value:"42",m_votemap:{offset:0,elems:[]}})
    ^C
    $ ./multi_paxos_system 2 0
    > binding id: 0 port: 5990
    < shim.debug_sending(0,{m_kind:one_a,m_round:2,m_inst:0,m_node:0,m_value:"",m_votemap:{offset:0,elems:[]}})
    < shim.debug_sending(1,{m_kind:one_a,m_round:2,m_inst:0,m_node:0,m_value:"",m_votemap:{offset:0,elems:[]}})
    < shim.debug_sending(0,{m_kind:one_a,m_round:4,m_inst:0,m_node:0,m_value:"",m_votemap:{offset:0,elems:[]}})
    < shim.debug_sending(1,{m_kind:one_a,m_round:4,m_inst:0,m_node:0,m_value:"",m_votemap:{offset:0,elems:[]}})
    < shim.debug_receiving({m_kind:one_a,m_round:4,m_inst:0,m_node:0,m_value:"",m_votemap:{offset:0,elems:[]}})
    < shim.debug_receiving({m_kind:one_a,m_round:15,m_inst:2,m_node:1,m_value:"",m_votemap:{offset:0,elems:[]}})
    < shim.debug_sending(1,{m_kind:one_b,m_round:15,m_inst:2,m_node:0,m_value:"",m_votemap:{offset:2,elems:[]}})
    system.server.propose(7)
    = 0
    > < shim.debug_receiving({m_kind:two_a,m_round:15,m_inst:2,m_node:1,m_value:"7",m_votemap:{offset:0,elems:[]}})
    < shim.debug_sending(1,{m_kind:two_b,m_round:15,m_inst:2,m_node:0,m_value:"7",m_votemap:{offset:0,elems:[]}})
    < shim.debug_sending(1,{m_kind:missing_decision,m_round:15,m_inst:2,m_node:0,m_value:"",m_votemap:{offset:0,elems:[]}})
    < shim.debug_receiving({m_kind:decide,m_round:15,m_inst:2,m_node:1,m_value:"7",m_votemap:{offset:0,elems:[]}})
    < system.server.decide(2,"7")
    < shim.debug_receiving({m_kind:decide,m_round:15,m_inst:2,m_node:1,m_value:"7",m_votemap:{offset:0,elems:[]}})
    < shim.debug_sending(1,{m_kind:missing_two_a,m_round:15,m_inst:0,m_node:0,m_value:"",m_votemap:{offset:0,elems:[]}})
    < shim.debug_sending(1,{m_kind:missing_two_a,m_round:15,m_inst:1,m_node:0,m_value:"",m_votemap:{offset:0,elems:[]}})
    < shim.debug_receiving({m_kind:decide,m_round:15,m_inst:0,m_node:1,m_value:"0",m_votemap:{offset:0,elems:[]}})
    < system.server.decide(0,"0")
    < shim.debug_receiving({m_kind:decide,m_round:15,m_inst:1,m_node:1,m_value:"42",m_votemap:{offset:0,elems:[]}})
    < system.server.decide(1,"42")

Terminal B:
-----------


    $ ./multi_paxos_system 2 1
    > binding id: 1 port: 5991
    < shim.debug_sending(0,{m_kind:one_a,m_round:1,m_inst:0,m_node:1,m_value:"",m_votemap:{offset:0,elems:[]}})
    < shim.debug_sending(1,{m_kind:one_a,m_round:1,m_inst:0,m_node:1,m_value:"",m_votemap:{offset:0,elems:[]}})
    < shim.debug_sending(0,{m_kind:one_a,m_round:3,m_inst:0,m_node:1,m_value:"",m_votemap:{offset:0,elems:[]}})
    < shim.debug_sending(1,{m_kind:one_a,m_round:3,m_inst:0,m_node:1,m_value:"",m_votemap:{offset:0,elems:[]}})
    < shim.debug_receiving({m_kind:one_a,m_round:3,m_inst:0,m_node:1,m_value:"",m_votemap:{offset:0,elems:[]}})
    < shim.debug_receiving({m_kind:one_a,m_round:8,m_inst:0,m_node:0,m_value:"",m_votemap:{offset:0,elems:[]}})
    < shim.debug_sending(0,{m_kind:one_b,m_round:8,m_inst:0,m_node:1,m_value:"",m_votemap:{offset:0,elems:[]}})
    < shim.debug_receiving({m_kind:two_a,m_round:8,m_inst:0,m_node:0,m_value:"0",m_votemap:{offset:0,elems:[]}})
    < shim.debug_sending(0,{m_kind:two_b,m_round:8,m_inst:0,m_node:1,m_value:"0",m_votemap:{offset:0,elems:[]}})
    < shim.debug_receiving({m_kind:decide,m_round:8,m_inst:0,m_node:0,m_value:"0",m_votemap:{offset:0,elems:[]}})
    < system.server.decide(0,"0")
    < shim.debug_receiving({m_kind:two_a,m_round:8,m_inst:1,m_node:0,m_value:"42",m_votemap:{offset:0,elems:[]}})
    < shim.debug_sending(0,{m_kind:two_b,m_round:8,m_inst:1,m_node:1,m_value:"42",m_votemap:{offset:0,elems:[]}})
    < shim.debug_receiving({m_kind:decide,m_round:8,m_inst:1,m_node:0,m_value:"42",m_votemap:{offset:0,elems:[]}})
    < system.server.decide(1,"42")
    EOF ON SOCKET
    < shim.debug_sending(0,{m_kind:one_a,m_round:9,m_inst:2,m_node:1,m_value:"",m_votemap:{offset:0,elems:[]}})
    < shim.debug_sending(1,{m_kind:one_a,m_round:9,m_inst:2,m_node:1,m_value:"",m_votemap:{offset:0,elems:[]}})
    < shim.debug_receiving({m_kind:one_a,m_round:9,m_inst:2,m_node:1,m_value:"",m_votemap:{offset:0,elems:[]}})
    < shim.debug_sending(0,{m_kind:one_a,m_round:11,m_inst:2,m_node:1,m_value:"",m_votemap:{offset:0,elems:[]}})
    < shim.debug_sending(1,{m_kind:one_a,m_round:11,m_inst:2,m_node:1,m_value:"",m_votemap:{offset:0,elems:[]}})
    < shim.debug_receiving({m_kind:one_a,m_round:11,m_inst:2,m_node:1,m_value:"",m_votemap:{offset:0,elems:[]}})
    < shim.debug_sending(0,{m_kind:one_a,m_round:13,m_inst:2,m_node:1,m_value:"",m_votemap:{offset:0,elems:[]}})
    < shim.debug_sending(1,{m_kind:one_a,m_round:13,m_inst:2,m_node:1,m_value:"",m_votemap:{offset:0,elems:[]}})
    < shim.debug_receiving({m_kind:one_a,m_round:13,m_inst:2,m_node:1,m_value:"",m_votemap:{offset:0,elems:[]}})
    < shim.debug_receiving({m_kind:one_a,m_round:4,m_inst:0,m_node:0,m_value:"",m_votemap:{offset:0,elems:[]}})
    < shim.debug_sending(0,{m_kind:one_a,m_round:15,m_inst:2,m_node:1,m_value:"",m_votemap:{offset:0,elems:[]}})
    < shim.debug_sending(1,{m_kind:one_a,m_round:15,m_inst:2,m_node:1,m_value:"",m_votemap:{offset:0,elems:[]}})
    < shim.debug_receiving({m_kind:one_a,m_round:15,m_inst:2,m_node:1,m_value:"",m_votemap:{offset:0,elems:[]}})
    < shim.debug_receiving({m_kind:one_b,m_round:15,m_inst:2,m_node:0,m_value:"",m_votemap:{offset:2,elems:[]}})
    system.server.propose(7)
    < shim.debug_sending(0,{m_kind:two_a,m_round:15,m_inst:2,m_node:1,m_value:"7",m_votemap:{offset:0,elems:[]}})
    < shim.debug_sending(1,{m_kind:two_a,m_round:15,m_inst:2,m_node:1,m_value:"7",m_votemap:{offset:0,elems:[]}})
    < shim.debug_sending(1,{m_kind:two_b,m_round:15,m_inst:2,m_node:1,m_value:"7",m_votemap:{offset:0,elems:[]}})
    = 1
    > < shim.debug_receiving({m_kind:two_a,m_round:15,m_inst:2,m_node:1,m_value:"7",m_votemap:{offset:0,elems:[]}})
    < shim.debug_sending(1,{m_kind:two_b,m_round:15,m_inst:2,m_node:1,m_value:"7",m_votemap:{offset:0,elems:[]}})
    < shim.debug_receiving({m_kind:two_b,m_round:15,m_inst:2,m_node:1,m_value:"7",m_votemap:{offset:0,elems:[]}})
    < shim.debug_receiving({m_kind:two_b,m_round:15,m_inst:2,m_node:1,m_value:"7",m_votemap:{offset:0,elems:[]}})
    < shim.debug_receiving({m_kind:two_b,m_round:15,m_inst:2,m_node:0,m_value:"7",m_votemap:{offset:0,elems:[]}})
    < shim.debug_sending(0,{m_kind:decide,m_round:15,m_inst:2,m_node:1,m_value:"7",m_votemap:{offset:0,elems:[]}})
    < shim.debug_sending(1,{m_kind:decide,m_round:15,m_inst:2,m_node:1,m_value:"7",m_votemap:{offset:0,elems:[]}})
    < system.server.decide(2,"7")
    < shim.debug_receiving({m_kind:missing_decision,m_round:15,m_inst:2,m_node:0,m_value:"",m_votemap:{offset:0,elems:[]}})
    < shim.debug_sending(0,{m_kind:decide,m_round:15,m_inst:2,m_node:1,m_value:"7",m_votemap:{offset:0,elems:[]}})
    < shim.debug_receiving({m_kind:decide,m_round:15,m_inst:2,m_node:1,m_value:"7",m_votemap:{offset:0,elems:[]}})
    < shim.debug_receiving({m_kind:missing_two_a,m_round:15,m_inst:0,m_node:0,m_value:"",m_votemap:{offset:0,elems:[]}})
    < shim.debug_sending(0,{m_kind:decide,m_round:15,m_inst:0,m_node:1,m_value:"0",m_votemap:{offset:0,elems:[]}})
    < shim.debug_receiving({m_kind:missing_two_a,m_round:15,m_inst:1,m_node:0,m_value:"",m_votemap:{offset:0,elems:[]}})
    < shim.debug_sending(0,{m_kind:decide,m_round:15,m_inst:1,m_node:1,m_value:"42",m_votemap:{offset:0,elems:[]}})

