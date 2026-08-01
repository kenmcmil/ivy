Isolating the fetch unit
========================

Motivation
----------

With dual issue activated, the whole-machine query for the PC-tracking invariant

    invariant (~spec_wrong & ~trace.st(trace.now).error) -> pc = trace.st(trace.now).pc

stops converging (Z3 churns; inlining the dc_* "deadly definitions" did not help).
The invariant is *true*: on an `issue_two` transition the PC advances by two and
the trace steps twice, and both fetched words are non-branch, so
`st(now+2).pc = st(now).pc + 2`. But its inductiveness now depends on the
*second* fetched word being coherent with the trace (`fetched1 = st(now.next).fetched`),
a deep, quantified memory-coherence fact that, mixed into the whole-machine VC,
blows up the solver. We localise the PC logic in a fetch isolate so that fact
becomes a clean assumption, proved separately in the parent.

The fetch unit
--------------

Role: own the PC and the speculation bit, decide how many instructions to issue,
advance the trace as instructions are fetched, and keep `pc = st(now).pc` on the
correct path.

Owned state: `pc`, `spec_wrong`. The `trace.step` calls (hence `now` advancement)
live *inside* the fetch isolate, because the number of steps (0/1/2) and the PC
advance must agree. The parent's tag bookkeeping (dcommit/mcommit/...) then reads
the post-step `now`.

Scope: minimal. Fetch owns only `pc`/`spec_wrong` (and the fetch-side ghost
monitor). The ID latches `d_*`/`d_*1` stay in the parent, driven by fetch's issue
decision.

Inputs (wires the parent drives)
--------------------------------

- fetched, fetch_valid            -- I-cache word0 (ic.fetch_data / fetch_valid)
- fetched1, fetch_valid1          -- I-cache word1 (ic.fetch_data1 / fetch_valid1)
- predicted_taken                 -- predictor output (bp), left arbitrary
- mispredict, redirect_pc         -- back-end branch resolution
                                     (redirect_pc = e_target if e_take else e_pc+1)
- ex_stall, dmem_stall, flush_in_pipe -- back-end stalls (gate fetching)

Outputs (read by parent)
------------------------

- pc                              -- drives ic.fetch_addr and bp.fetch_pc
- issue0, issue1                  -- lane-0 / lane-1 issued this cycle; the parent
                                     latches d_valid := issue0, d_valid1 := issue1,
                                     d_ir := fetched, d_ir1 := fetched1,
                                     d_shadow := (fetch's shadow), etc.

Protocol (all in existing ghost state: trace, now, error, spec_wrong)
---------------------------------------------------------------------

Assumptions the parent discharges (guarantees TO fetch):

  A0 (word0):   ~error & ~spec_wrong & fetch_valid
                    -> fetched = st(now).fetched
  A1 (word1):   ~error & ~spec_wrong & fetch_valid1 & st(now).opcode ~= 6
                    -> fetched1 = st(now.next).fetched
      (guarded by "current instruction is non-branch", so now.next is the
       sequential sibling at pc+1; issue_two establishes that guard via A0, so
       it is always available where fetch uses fetched1)
  A2 (redirect): mispredict & ~error -> redirect_pc = st(now).pc
      (mispredict clears spec_wrong and does not step the trace, so the corrected
       PC must equal the current trace PC; already effectively proved today)

Guarantee fetch provides (to parent):

  G (pc-tracking): ~spec_wrong & ~error -> pc = st(now).pc

  plus, proved locally in fetch from A0/A1:
       issue_two -> st(now) and st(now.next) are both non-branch
  which is the fact the monolithic solver cannot currently reach.

A1 is the crux: as a standalone parent obligation it is "the same as A0 but at
pc+1", which the parent already proves for word0.

Plan / steps
------------

1. (this file) pin the interface, A0-A2, G, and the ownership decisions.
2. Factor pc + spec_wrong + the fetch/issue/trace.step logic into a nested
   isolate `cpu.fetch` with the wires above; move the pc-tracking invariant and
   the "issue_two -> non-branch" lemma inside it as guarantees; state A0-A2 as
   its assumptions (`with this, trace, ...`).
3. Discharge A0/A1/A2 in the parent. A0/A2 should fall out of the existing proof;
   A1 is the new, isolated obligation -- attack it alone with icache_output1 +
   the memory-coherence invariants.
4. Re-check cpu.fetch and the parent (isolate this) separately; iterate on CTIs.

Risks / things to watch
-----------------------

- Monitor ordering: fetch's ghost monitor advances `now`; the parent's tag
  monitor reads it. Keep the established discipline (read validity bits via `old`,
  treat combinational wires as frozen at pre-state) so the split is insensitive
  to monitor order.
- A1's coherence still needs the mcommit->now memory bridge at pc+1; if it does
  not fall out cleanly, add it as an explicit parent lemma (mirroring word0).
- The predictor (`bp`) is already a sub-isolate; `cpu.fetch` reads its output as
  an assumption-free arbitrary input, same as today.
