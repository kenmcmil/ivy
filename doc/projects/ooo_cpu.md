In this project, we will develop a simple out-of-order of the dual-issue CPU in dual_issue_cpu_ref.ivy.
The new design will be ooo_cpu_ref.ivy.

Architecture
------------

The design will use Tomasulo's algorithm with a re-order buffer.

Design components:

The micro-architectural state includes:

1) Architectural pc and register file.
2) Register renaming table. Register names are just pointers into the ROB.
3) ROB. In-order queue of instructions in flight (with branch prediction). Stores instruction results.
4) Reservation stations. Keyed to ROB. Collect operands of instructions when available.  

Operational units:

1) Fetch stage -- similar to existing design.

2) Decode/rename/dispath stage (replaces decode stage in dual_issue_cpu design)

This stage dispatches up to two instructions fetched from the icache in
the fetch stage. Dispatched instructions are queued in the ROB and
destination registers are renamed in the renaming table.

3) Instruction issue unit

Manages the reservation stations and issues instructions with ready operands to
execution units. LD/ST/FLUSH instructions are issued in order. 

4) Execution units

Several ALU operation units and one MEM unit. The MEM unit uses a LD/ST buffer.
Branch unit signals mispredict to retire unit (this can be a combinational path). 


5) Retire unit.

Retires instruction form RB in order. Writes results to architectural register file
and clears the destination entry in the renaming table, if the tag matches the entry.
Also handles canceling instructions that follow a mispredict.

6) I-cache and D-cache

We will use the existing idcache.ivy for this.

Development approach
--------------------

Since this is a complex design, we will develop it in stages, maintaining the proof
in each stage.

Proposed stages:

1) ALU instructions only (disable LD/ST/BRANCH/FLUSH)

This will test the basic Tomasulo implementation and proof approach. No MEM unit and no branch predictor.

2) Add conditional branch instruction.

3) Add memory instructions

Proof approach
--------------

We will use the reference tagging approach. Micro-architectural
elements will contain tags pointing into abstract instruction trace. For example
each entry in the ROB has a tag. The tag tells us the correct operand and result
values for the instruction.


Status
------

Stage 1 (2026-09-17): `ooo_cpu_ref.ivy` -- ALU ops only, single-wide dispatch,
one ALU with a one-cycle latch, 4-entry ROB with the reservation-station fields
per entry, oldest-first issue, result broadcast on completion. `ivy_check` OK
(~17 s). Translates with `ivy_to_rtl` (the broadcast arrays lower to register
banks -- a translator extension made for this) and `sim_cpu.sh ooo_cpu_ref
prog_alu.hex` shows dispatch/issue/retire live and the register file matching
the program's expected results. The stage-1 ISA treats opcodes 4..7 as NOPs.
A hand-written SystemVerilog golden (`ooo_alu_golden.sv`) is proven
combinationally equivalent to the emitted RTL, register for register
(`check_ooo_golden.sh`, via rtlil_eqv; 524 cones). To make that check
state-independent the Ivy clock action is ordered complete/retire/issue/
dispatch/fetch with wire-based reads, so it has exactly nonblocking semantics.

The stage-1 design is frozen as `ooo_cpu_alu_ref.ivy` (the golden and
`check_ooo_golden.sh` target it).

Stage 2 (2026-09-17): `ooo_cpu_ref.ivy` adds BEQZ with the bimodal predictor
`bp` (predict at fetch, train at retire). A branch is a one-operand ALU op;
the ALU records its outcome in `rob_take`, the prediction rides in `rob_pred`,
and a mispredicted branch is resolved AT RETIRE: it squashes the whole ROB
(all younger), clears the rename table, kills the ALU and fetch latches and
redirects the pc. Proof: shadow bits per ROB entry + `d_shadow`, `spec_wrong`,
and a ghost `mp_idx` naming the single unresolved mispredicted branch;
shadowed entries are a suffix strictly younger than it, so the head is never
shadowed. `ivy_check` OK (~2 min 20 s). RTL translates (rob_busy/rat_valid
become register banks because of the squash's whole-array clear) and
`sim_cpu.sh ooo_cpu_ref prog_br.hex` runs a countdown loop with a
mispredicting back-branch correctly. The stage-2 golden `ooo_beqz_golden.sv`
(with the predictor as a `bp` submodule) is proven equivalent by
`check_ooo_golden.sh ooo_cpu_ref ooo_beqz_golden.sv` (605 cones, including
the 32 bits of bp.bht).

Next: stage 3 (LD/ST via idcache with an in-order LD/ST buffer, FLUSH,
restore ddirty/error). Later refinements: resolve mispredicts at execution
(needs rename-table recovery), dual-wide dispatch, more ALUs.
