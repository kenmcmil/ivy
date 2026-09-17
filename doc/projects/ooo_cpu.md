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

Stage 2 is frozen as `ooo_cpu_beqz_ref.ivy`.

Stage 3a (2026-09-17): `ooo_cpu_ref.ivy` restores the full ISA (LD/ST/FLUSH,
`ddirty`/`error`) with the `idcache` module for the I/D caches, but WITHOUT a
LD/ST queue: memory instructions execute in order AT THE HEAD of the ROB. A
LD/ST/FLUSH entry is never issued to the ALU; when it is the head and its
operands are ready it presents its request to idc and, if idc does not stall,
completes and retires in one cycle (a LD writes rf, broadcasts its data to
waiting entries -- a second broadcast source alongside the ALU -- and bypasses
it to a same-cycle dispatch). A FLUSH stalls fetch from the moment it is
fetched until it retires, so it is always the youngest instruction in flight.
Proof: idc.mem/ddirty = st(commit).mem/ddirty exactly (memory ops are retire
ops); fetch coherence needs only two one-step invariants -- with no FLUSH in
flight every in-flight store leaves its address dirty at now, hence under the
fetch condition memory at that address is unchanged across [commit, now).
Every trace-relating invariant is guarded by ~st(now).error. `ivy_check` OK
(~3.5 min). RTL translates; `sim_cpu.sh ooo_cpu_ref prog_mem.hex` (store,
dependent load, add on the load, store, FLUSH, load) matches. Two CTI rounds:
memory ops were marked `issued` at dispatch, and the pending-operand invariant
had to say the producer is a register writer (else a consumer of a *store* is
imaginable, and a store retires without broadcasting). The stage-3a golden
`ooo_mem_golden.sv` (cpu + bp + the idcache/main_mem/ic/dc golden modules of
dual_issue_golden.sv with completed reset lists) is proven equivalent by
`check_ooo_golden.sh ooo_cpu_ref ooo_mem_golden.sv` (5947 cones, ~2 min).

Stage 3a is frozen as `ooo_cpu_mem_ref.ivy` (its golden retargeted to it).

Stage 3b (2026-09-17): `ooo_cpu_ref.ivy` adds the LD/ST queue. The queue is
the ROB order itself: the memory port serves the oldest unperformed memory op
(a priority scan from the head, like issue selection). A LOAD performs as soon
as it is that op and its address is ready -- speculatively, ahead of older ALU
ops and branches -- writing its value into the entry (rob_val/rob_done),
broadcasting it and bypassing it to a dispatching consumer; it then retires
like an ALU op. ST/FLUSH still perform at retire (memory is never written
speculatively), so a load behind an unretired store waits for it (no
store-to-load forwarding). Proof: the MEMORY ANALOGUE OF THE RENAME TABLE as
ghost state -- mrat_valid/mrat_idx(A) (youngest in-flight store to A) with
`~mrat_valid(A) -> st(now).mem(A) = st(commit).mem(A)` and `mrat_valid(A) ->
st(now).mem(A) = st(tag(mrat_idx(A))).b_val`, plus per load ld_src_valid/
ld_src(I) (the youngest OLDER store to its address, captured from mrat at
dispatch, released when it retires) with `~ld_src_valid(I) -> st(tag(I)).mem(a)
= st(commit).mem(a)` and `ld_src_valid(I) -> st(tag(I)).mem(a) =
st(tag(ld_src(I))).b_val`, and the "youngest"/"no older store" side conditions.
A performing load is the oldest unperformed memory op, an unretired older
store is unperformed, so the load is unbound and idc's value is its reference
value. `ivy_check` OK (~10 min). RTL translates; `sim_cpu.sh ooo_cpu_ref
prog_lsq.hex` shows an independent load performing before an older ALU chain
retires and a load behind a store to the same address waiting for it. One CTI
round: `rob_done_issued` needs a load exclusion. The stage-3b golden
`ooo_lsq_golden.sv` is proven equivalent by `check_ooo_golden.sh ooo_cpu_ref
ooo_lsq_golden.sv` (5947 cones, ~80 s).

Stage 3b is frozen as `ooo_cpu_lsq_ref.ivy` (its golden retargeted to it).

Stage 3c (2026-09-17): `ooo_cpu_ref.ivy` adds STORE-TO-LOAD FORWARDING. A load
is performable when its address is ready and no older unperformed memory op
BLOCKS it (a FLUSH, or a store whose address is not yet known); it passes
older stores to other addresses and older loads. The youngest older
unperformed store with a known matching address is its forwarding source; if
there is one the load takes that store's data (once ready) without touching
the cache, else it reads idc. Two memory slots work in parallel: the CACHE
slot serves the oldest performable op needing idc (ST/FLUSH at the head or a
non-forwarding load), the FORWARDING slot the oldest performable forwarding
load -- so a store missing in the cache does not hold up the loads that
depend on it (with a single oldest-first slot, forwarding never fired in
practice: the stalled store at the head owned the slot). Three result
broadcasts (ALU, cache load, forwarded load) and three dispatch bypasses.
Proof: no new ghost state -- the datapath's associative search is tied to
the ld_src ghost by derived invariants: the forwarding slot's correct-path
load forwards exactly from ld_src (`sel_fwd_src`, from "every older store's
address is known" + ld_src_youngest/ld_src_trk), and the cache slot's load
is unbound (`sel_nofwd`, from ld_nosrc_nostore); a forwarded value is then
st(tag(ld_src)).b_val = the load's reference value. `ivy_check` OK (~39 min
sharing the machine with another proof; the single-slot variant took
17.5 min alone), zero CTIs. RTL translates; `sim_cpu.sh ooo_cpu_ref
prog_fwd.hex` shows the forwarding slot completing a load while its source
store is the head stalled on a D-cache miss. The stage-3c golden
`ooo_fwd_golden.sv` is proven equivalent by `check_ooo_golden.sh ooo_cpu_ref
ooo_fwd_golden.sv` (5947 cones, ~2.5 min).

Next: resolve mispredicts at execution (rename-table recovery), dual-wide
dispatch, more ALUs.
