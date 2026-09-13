Dual-issue pipeline conversion
==============================

This project converts `doc/examples/hardware/dual_issue_cpu_ref.ivy` from a
single-issue 5-stage pipeline into a 2-wide (dual-issue) in-order superscalar,
verified against the same ISA reference by the reference-tagging method. The
two-word I-cache line already in place (a nested `cpu.ic` isolate) is what makes
a two-instruction fetch possible; this project widens the rest of the pipeline.

Governing principle
-------------------

Grow the machine one increment at a time, keeping `ivy_check <file>` green after
each. Every hazard is first handled by **splitting the bundle** -- issue the
older instruction (lane 0), recirculate the younger (lane 1) as the next
bundle's lane 0. Splitting is always available, so the machine is *correct* at
every step and each later relaxation (bypass, dual memory, branches) only raises
IPC, never correctness. Do the hard proof change (the tag scheme) first, in
isolation, before any new hazard logic exists.

What does NOT change
--------------------

- **The ISA model and the `trace` isolate are untouched.** The reference still
  executes one instruction per step; the trace is still a linear sequence of ISA
  states. Dual-issue is entirely implementation-side.
- **The tag scheme generalizes, it is not replaced.** See below.

Design decisions (locked)
-------------------------

- 2-wide, in-order.
- **Aligned even/odd pairs only** (early steps). An even PC fetches the pair
  `[A, A+1]`; an odd PC issues a single instruction in lane 0. Unaligned packing
  (a fetch buffer that pairs any two consecutive instructions) is the last,
  perf-only step.
- **One D-cache port and one branch unit.** At most one memory op and one branch
  per bundle, enforced structurally at issue (split otherwise).
- **Split-on-hazard first.** Intra-bundle bypass and one-mem-per-bundle are later
  relaxations, not in the first working machine.
- **Lane 0 is older.** In an aligned even pair, address `A` (even) is older and
  goes in lane 0; `A+1` (odd) is younger and goes in lane 1. On a split, lane 1
  becomes the next bundle's lane 0.

The tag scheme (the heart of the proof)
---------------------------------------

Today the boundary counters `commit <= mcommit <= ecommit <= dcommit <= now`
each advance by at most one per cycle, each stage holds at most one instruction,
and the occupied tags form a contiguous run. Generalize as follows:

- **Each boundary counter advances by 0, 1, or 2 per cycle** -- the number of
  (non-shadowed) instructions that crossed that boundary. Advancing by two is
  `succ` applied twice; the abstract `tag` type already supports this.
- **Each stage holds a contiguous run of 0..2 tags.** Stage occupancy is the
  half-open interval between its two bounding counters; its size is
  `upper - lower in {0,1,2}`. E.g. WB holds tags `[commit, mcommit)`.
- **Per-lane invariant.** Lane `j` of a stage whose lower bound is `base` holds
  `trace.st(base + j)` (for `j < size`). This is the per-element invariant of the
  method, now indexed by lane. Lane validity: lane `j` valid iff `j < size`.
- **Contiguity is preserved** across the whole pipeline: the union of all stage
  runs is still one contiguous run `[commit, now)`. The structural tag invariants
  (currently `w_valid -> commit.succ(mcommit)`, etc.) become run-size facts
  relating each pair of adjacent counters to the number of valid lanes in the
  stage between them.

This is the single largest proof change and it is mechanical. It is done and
verified in Step 1, before any dual-issue behavior exists.

### Tag invariants (the adjacency chain)

Rather than incrementing boundary counters by two (`t := t.next.next`), the
simpler formulation carries a **ghost tag on every lane latch**, propagated
stage to stage with the instruction. Correctness is then stated as *local
relations between adjacent lanes* in program order. List the lanes oldest-first
across the pipeline -- `W0, W1, M0, M1, E0, E1, D0, D1` (WB is oldest, about to
retire; within a stage lane 0 is older than lane 1) -- and consider each
adjacent pair, whether within a stage (`X0,X1`) or across a stage boundary
(`X1,Y0`). The invariant is uniform:

- **Every adjacent pair (older, younger) satisfies `younger.tag = older.tag`
  (younger is a bubble) or `succ(older.tag, younger.tag)` (younger is a real
  instruction).** A bubble lane carries a *duplicate* of its older neighbor's
  tag, so it advances the run by zero; a valid lane advances it by one.
- Consequently the valid lanes' tags form a **contiguous ascending run**, and the
  oldest tag is the retire pointer `commit`. The counter advance "by 0/1/2 per
  cycle" is then just the number of valid lanes that crossed a boundary -- no
  explicit two-step tag arithmetic is needed.
- The existing single-issue facts are the one-lane special case: e.g.
  `w_valid -> commit.succ(mcommit)` is exactly "the WB lane and the MEM lane hold
  successor tags", which generalizes to the `(X1,Y0)` cross-boundary pairs.

Per-lane data invariants then read against each lane's own tag: a valid lane `L`
holds `trace.st(L.tag).fetched`, its operands equal the trace's recorded values
at `L.tag`, and so on -- one fact per lane, the reference-tagging pattern indexed
by lane.

Datapath changes (per stage)
----------------------------

Each pipeline latch becomes a **lane-0/lane-1 pair**, each lane with its own
valid bit and (ghost) tag:

- **IF / fetch.** `ic` gains a dual read port: return both words of the addressed
  line, `fetch_data0`/`fetch_data1` with per-word validity, from the even base
  `pc & ~1`. Alignment: even PC issues both words (lane 0 = `A`, lane 1 = `A+1`);
  odd PC issues only the odd word in lane 0. `fetched`/`fetch_active`/
  `ifetch_stall` become per-lane.
- **ID.** `d_ir/d_valid/d_pred/d_pc` -> lane-0/1 pairs. Two decoders. Issue logic
  and hazard detection live here (see below).
- **EX.** `e_ir/e_valid/e_pred/e_pc` -> pairs; two ALUs (or ALU + AGU). Branch
  resolution for the bundle's (single) branch.
- **MEM.** `m_ir/m_valid/m_res/m_addr/m_store` -> pairs; but the single D-cache
  port means at most one lane does memory (structural limit).
- **WB.** `w_ir/w_valid/w_val` -> pairs; two register-file write ports. On a
  same-destination bundle (WAW), the younger lane (1) wins.

`ic` is an isolate, so its dual-read change is made and re-proved locally
(`ivy_check isolate=cpu.ic`). Its data invariant `hard` already covers both
words of a full line, so exposing both outputs is a natural extension of the
existing guarantee `icache_output` (one guarantee per output word).

Issue logic and the split rule
------------------------------

In ID, decide per cycle whether to issue one or two instructions. Issue **both**
lanes of an aligned even pair only when every enabling condition holds; otherwise
**split** (issue lane 0, hold lane 1 as next cycle's lane 0). The conditions are
relaxed one per step:

- Step 2: both simple (ALU/NOP), independent (distinct src/dst regs), non-branch,
  non-memory, and PC even (aligned).
- Step 3 removes the independence condition (adds intra-bundle bypass).
- Step 4 allows one memory op in the bundle.
- Step 5 allows a branch in the bundle.

Splitting is a bubble in lane 1 of every downstream stage for that cycle; the
younger instruction re-enters as lane 0 next cycle. Because a split is always
legal, correctness never depends on any relaxation.

Speculation with bundles
------------------------

The shadow-bit machinery extends per lane. A taken branch in lane 0 squashes
lane 1 (younger, same bundle) and redirects fetch; the predictor predicts on the
bundle. The core obligation is unchanged in spirit -- shadowed state is never
committed -- now stated per lane. With one branch unit, a bundle with two
branches splits, so at most one branch resolves per cycle.

Steps (each ends with `ivy_check OK` + a `sim_cpu.sh` sanity run)
----------------------------------------------------------------

1. **Two-lane latch skeleton, still single-issue.** Replicate every pipeline
   *latch* (`d_*`/`e_*`/`m_*`/`w_*`) into a lane-1 twin, propagated stage to stage
   as a bubble, with issue width hardwired to 1 (`d_valid1` is always false, so
   every `*_valid1` is provably false). The computed lane-1 latch values
   (`m_res1`, `w_val1`, ...) are don't-cares while the lane is empty, so they are
   left as placeholders (0); the real lane-1 combinational datapath (operand
   reads, ALU, D-cache access) and the `ic` dual read port arrive in Step 2 with
   the issue logic that consumes them. The **boundary-counter tags are unchanged**
   here: with lane 1 bubbled, the existing single-lane invariants are exactly the
   `(X1,Y0)` special case of the adjacency chain, so no tag reformulation is
   needed yet. Behavior is identical to today; the deliverable is a verified,
   RTL-translatable two-lane datapath skeleton (`ivy_check OK`, `sim_cpu.sh`
   unchanged) with `~d_valid1 & ~e_valid1 & ~m_valid1 & ~w_valid1` proved.

2. **Enable dual issue (easy case) + the per-lane tag scheme + `ic` dual read.**
   Fill in the lane-1 combinational datapath and the `ic` dual read port
   (`fetch_data1`/`fetch_valid1`), switch the ghost bookkeeping to the per-lane
   propagated-tag adjacency chain (so a bubble carries a duplicate tag and a valid
   lane advances the run by one), and turn issue width to 2 for the easy case:
   both lanes issue when both are simple (ALU/NOP), independent, non-branch,
   non-memory, and aligned (even PC); split otherwise. `commit` can now retire two
   per cycle. Sanity: `sim_cpu.sh` shows 2 retirements/cycle on an
   independent-ALU program.

3. **Intra-bundle RAW via bypass.** Forward lane 0's result to lane 1's operand
   read instead of splitting on a RAW dependence. See "Step 3 detail" below.

4. **One memory op per bundle.** Allow a load/store in one lane paired with an
   ALU in the other, over the single D-cache port (split if both are memory).
   Extend the D-cache / `ddirty` / `error` coherence invariants and settle
   store/load ordering and FLUSH placement within a bundle.

5. **Branches in a bundle.** Allow a branch in the bundle: taken branch in lane 0
   squashes lane 1 and redirects; extend shadow-bit speculation and the predictor
   interface to bundles; split if both lanes are branches.

6. **Unaligned packing (optional, perf).** A small fetch buffer pairs any two
   consecutive instructions regardless of alignment. Correctness-trickiest fetch
   case, pure IPC gain, so last.

Steps 3-6 each fall back to split, so they are independent and reorderable.

Step 3 detail: intra-bundle RAW bypass
--------------------------------------

Today `issue_two` requires `f_indep` -- lane 1 must not read lane 0's
destination -- so a dependent aligned pair splits. Step 3 removes that
restriction by forwarding lane 0's freshly-computed ALU result to lane 1's
operand, so a dependent simple pair issues together.

Why it is sound (the reference view). Lane 1's tag is `e1_tag = ecommit.next`,
so `st(e1_tag).rf` already has lane 0 (tag `ecommit`) applied. If lane 0 writes
lane 1's source register R (`st(ecommit).rd = R`), then
`st(e1_tag).rf(R) = st(ecommit).res` -- exactly lane 0's ALU result. In hardware
that result is `e_res` (lane 0's EX ALU output, available the same cycle), and we
already prove `e_res` tracks `st(ecommit).res`. So forwarding is the correct
value; if lane 0 does *not* write R, the register-file read is correct as before.

Datapath changes:

- Factor lane 0's ALU result into a wire `e_res` (currently computed inline in
  the posedge as `m_res := e_a + e_b if ...`); use it both for the MEM latch and
  the bypass.
- Bypass muxes in EX: `e_a1_fwd = (e_res if (e_lane0_wr & e_rd = e_ra1) else
  e_a1)` and likewise `e_b1_fwd` for `e_rb1`, where `e_lane0_wr = e_valid &
  e_opcode in {1,2,3}`. Lane 1's ALU `e_res1` consumes the forwarded operands.
- Relax `issue_two`: drop `f_indep` entirely (any aligned simple non-branch
  non-memory pair issues). WAW (`e_rd = e_rd1`) is already handled -- WB writes
  lane 1 second, so the younger write wins and `rf` matches the reference.

Proof changes:

- Add EX-result tracking `[eres_trk] (e_valid & ~ex_stall & e_opcode in {1,2,3}
  & ~error) -> e_res = st(ecommit).res` (follows from the operand-tracking
  `ea_trk`/`eb_trk` + the trace `res`-consistency).
- Rework `ea1_trk`/`eb1_trk` to the forwarded operand: they become a case split
  on the mux -- forwarded (`= e_res = st(ecommit).res = st(e1_tag).rf(e_ra1)`) or
  register-file (`= st(commit).rf(e_ra1) = st(e1_tag).rf(e_ra1)`, no writer in the
  window). Keep the zero-delay `with rf_track` (and add `with eres_trk` for the
  forwarded case).
- Drop `d_indep`/`e_indep` (dependence is now allowed, so they are no longer
  true and no longer needed).

Verification order (keep `ivy_check` green at each sub-step):

  3a. Add `e_res` wire + the bypass muxes, but keep `f_indep` in `issue_two` (so
      the bypass path is present but never exercised). Verify unchanged.
  3b. Add `eres_trk`; rework `ea1_trk`/`eb1_trk` for the mux. Verify (still with
      `f_indep`, so the forwarded case is dormant but provable).
  3c. Drop `f_indep` from `issue_two` and drop `d_indep`/`e_indep`. Verify;
      iterate CTIs.
  3d. Full check + `sim_cpu.sh` on a program with a genuine RAW aligned pair
      (e.g. `LI r1 ; ADD r2,r1,r1` at an even/odd pair) -- confirm `issue_two`
      now fires on the dependent pair.

Risks: the mux makes `ea1_trk` a case split (may be slow -- the array-read
tracking discipline and zero-delay `with` are the mitigation); WAW correctness
rests on the lane-1-second write ordering in WB (already in place, but re-confirm
`rf_track` preserves with two same-cycle writes).

Status (2026-09-12): Step 3 COMPLETE. The memory subsystem was also replaced by
the reusable idcache module (both fetch lanes) along the way.

  memory  DONE (2393d79): the inline I-cache (the failing `ic` isolate) and
      write-back D-cache were replaced by an `idcache` instance `cpu.idc`, wiring
      BOTH fetch lanes (idc.fetch_data0/1). The CPU relates only idc's abstract
      mem/ddirty to the reference at the MEM tag; idc's guarantees supply
      dual-lane fetch + LD coherence. `ivy_check` OK (~33s).
  3a  DONE (77ea84c): the bypass datapath (e_res wire, e_a1_fwd/e_b1_fwd muxes,
      m_res := e_res), kept dormant behind f_indep. isolate=this verified OK.
  3b  DONE (folded into the idcache/derived-invariant work): eres_trk
      (e_res = st(ecommit).res) added with `with ea_trk, eb_trk`; ea1_trk/eb1_trk
      re-pointed to the forwarded operands e_a1_fwd/e_b1_fwd with `with eres_trk`.
      Several tracking invariants are now `derived invariants`, which is why the
      cpu consecution checks quickly.
  3c  DONE (fc3a794): dropped `f_indep` from issue_two and removed d_indep/e_indep
      (plus the now-dead f_indep/f_lane0_wr/f_rd0/f_ra1/f_rb1/f_rd1 wires). The
      bypass is live: a dependent aligned pair issues together. `ivy_check` OK
      (~95s; the slowdown is the bypass-mux case split, no extra `with` hints).
  3d  DONE (038d0db): sim_cpu.sh on dual_dep_prog.hex (a looped intra-bundle
      RAW-dependent pair) confirms issue_two fires warm -- pc jumps 2 -> 4 every
      iteration and both lanes retire in one cycle (r3=10, r4=15, the forwarded
      value). Added a dual_issue_cpu_ref to_rtl regression + a check regression.
      sim_cpu.sh now auto-detects the main-memory array (\mem vs \real_mem).

Step 4 detail: one memory op per bundle
---------------------------------------

Allow a LD/ST/FLUSH in one lane paired with an ALU op in the other, over the
single idc data port; SPLIT if both lanes are memory (at most one memory op per
bundle). Correctness never depends on it (a split is always legal), so it is a
pure IPC gain. Because at most one memory op is ever in a bundle, there is never
a store+load or load+store in the same bundle -- intra-bundle memory ordering is
a non-issue; the only new hazards are register RAW between the lanes, handled by
the Step-3 bypass for ALU producers. Staged like Step 3:

  4a  Memory op in LANE 0 (even), ALU in lane 1 (odd). Smallest delta: the
      existing single-issue memory datapath and idc port wiring are already driven
      by lane 0; lane 1 stays a pure ALU.
      - Relax issue_two: lane 0 may be any NON-BRANCH op (~(f_op0 = 6)) -- simple
        or LD/ST/FLUSH; lane 1 stays simple (opcode 0/1/2/3). Add the UNBYPASSABLE
        LOAD-USE split: if lane 0 is a LD (f_op0 = 4), require lane 1 not read its
        destination (f_rd0 ~= f_ra1 & f_rd0 ~= f_rb1) -- a load result is not
        available in EX, so it cannot be forwarded; split instead. (WAW is handled
        by WB writing lane 1 second, so no f_rd1 check is needed.)
      - Relax the lane-0 opcode-class invariants from simple to NON-BRANCH
        (~(*_opcode = 6)); lane 1 stays simple. ("No branch in a dual bundle's
        lane 0" is still the Step-5 boundary.)
      - No datapath change: m_addr/m_store/m_res (lane 0), the idc request/addr/
        data wiring, dmem_stall, and the lane-0 LD path (w_val := idc.read_data)
        already exist and are opcode-guarded; m0_wr/w0_wr already include op 4.
      - Verify ivy_check + a sim showing a {LD/ST, ALU} bundle issuing.

      4a  DONE. Two subtleties surfaced, neither giving a fast counterexample --
          the symptom was a pc_track CONSECUTION blow-up (>160s), found by ruling
          out issue_two cases until it passed:
          (1) A FLUSH in lane 0 must ALSO split -- a FLUSH invalidates the lane-1
              fetch (the sibling word is not valid until the FLUSH completes, the
              same reason fetch stalls behind a FLUSH in the pipe). Fixed by adding
              `& f_op0 ~= 7` to issue_two. This was the cause of the blow-up (a true
              bug); a memory op in lane 0 is otherwise fine.
          (2) The load-use split must be carried into the pipe as invariants
              d_ld_use/e_ld_use (the load-only analog of the old d_indep/e_indep):
              `*_valid1 -> ~(*_opcode = 4 & (*_rd = *_ra1 | *_rd = *_rb1))`. Without
              them ea1_trk/eb1_trk fail, because for a lane-0 LOAD the bypass is
              inactive and the register-file read is stale unless lane 0 does not
              write that source. issue_two establishes it; these propagate it.
          Sim: dual_mem_prog.hex loops {2,3}=ST;ADD and {4,5}=LD;ADD; warm, the pc
          jumps 2 -> 4 -> 6 and the LD returns the stored value. ivy_check OK ~36s.

  4b  Memory op in LANE 1 (odd), ALU in lane 0 (even). Adds the lane-1 memory
      machinery and the port mux.
      - Make m_addr1/m_store1 real (from e_a1_fwd/e_b1_fwd -- the bypass already
        forwards lane 0's ALU result into a lane-1 address/data operand); route a
        lane-1 LD result to w_val1 := idc.read_data.
      - Mux the idc data port to whichever lane holds the memory op (mem_l1 =
        m_valid1 & m_opcode1 in {4,5,7}); exactly one memory op per bundle makes
        the mux well-defined.
      - Per-lane MEM tracking: m_addr1 = st(m1_tag).mem_addr, m_store1 =
        st(m1_tag).b_val (opcode-guarded), lane-1 LD w_val1 = st(w1_tag).mem(...).
        Confirm idc.mem/ddirty = st(mcommit) holds with the store at the lane-1
        tag (mcommit still advances by 2; idc applies the one store in lockstep).
      - Relax lane-1 opcode invariants to non-branch; extend flush_in_pipe to a
        lane-1 FLUSH.
      - issue_two: allow lane 1 memory when lane 0 is ALU; SPLIT if both are
        memory. A lane-1 memory address depending on lane 0's ALU result is
        forwarded via e_a1_fwd, so {ADD, LD [r]} issues together.
      - Verify ivy_check + a sim showing an {ALU, LD/ST} bundle.

      4b  DONE (verified first try, ivy_check OK ~35s, no CTIs). Notes vs the plan:
          - flush_in_pipe did NOT need lane-1 terms: issue_two splits every FLUSH
            (f_op0 ~= 7 & f_op1 ~= 7), so a FLUSH only ever rides a single-issue
            lane-0 bundle, already covered.
          - The port mux is on mem_l1 = m_valid1 & m_opcode1 in {4,5} (FLUSH never
            reaches lane 1). read/write/flush_req OR the two lanes' terms.
          - Key supporting invariants: relax BOTH lanes' opcode-class invariants to
            ~=6 & ~=7 (non-branch, non-flush), and add d/e/m_one_mem
            (~(mem(op) & mem(op1))) so (a) the idc port has a single request
            [one_data_op] and (b) when lane 1 is the memory op, lane 0 is not a
            store, so st(m1_tag).mem = st(mcommit).mem and the lane-1 LD reads the
            right value. Lane-1 MEM tracking (m_addr1/m_store1 = st(m1_tag).*) and
            the lane-1 LD w_val1 mirror lane 0 and follow from ea1_trk/eb1_trk.
          - m1_wr/w1_wr gain opcode 4 (a lane-1 load is a register writer, for
            inter-bundle hazard detection).
          Sim: dual_mem_l1_prog.hex loops {2,3}=ADD;ST and {4,5}=ADD;LD with the
          lane-1 address forwarded from lane 0; warm, pc jumps 2 -> 4 -> 6 and the
          lane-1 LD returns the value the lane-1 ST wrote. Step 4 COMPLETE.

  Risks: load-use (4a) is the only genuinely new hazard, handled purely by the
  issue-time split. Inter-bundle load-use is already covered by m0_wr/w0_wr (4b
  adds op 4 to m1_wr/w1_wr). Adding a memory opcode to a lane widens the MEM/WB
  case split (watch for slowdown, as in 3c). Keep m_addr1/m_store1 point-writeable
  and the port mux combinational so ivy_to_rtl stays clean; re-run sim after each
  sub-step.

Risks / things to watch
-----------------------

- **Tag arithmetic.** The abstract `tag` type is used with `succ` and `<=` only;
  0..2 advance needs `succ` twice and run-size (`upper - lower <= 2`) reasoning.
  Confirm the trace isolate's `with` clause and lemmas support this; add a small
  ordered-arithmetic fact if the "run size <= 2" reasoning is not automatic.
- **Spurious CTIs from lane-1 freedom.** As with the I-cache inputs, an
  abstract/uninitialized lane 1 can produce spurious counterexamples; keep lane 1
  provably bubbled in Step 1 (a structural invariant `~lane1_valid`) and relax it
  only in Step 2.
- **RTL-translatability.** Keep all ghost lane/tag updates in `specification`;
  the two-lane datapath must stay point-writeable (two RF write ports = two point
  writes) so `ivy_to_rtl` still emits clean memories. Re-run `sim_cpu.sh` after
  each step.
- **`ic` interface churn.** The dual read port changes the `cpu.ic` boundary;
  re-audit with `ivy_show isolate=cpu.ic` after Step 1.
