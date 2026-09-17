// Hand-written "golden" SystemVerilog model of ooo_cpu_ref.ivy at stage 3c: the
// out-of-order core with the full ISA -- ALU ops, BEQZ with a bimodal branch
// predictor (mispredicts resolved at retire), and LD/ST/FLUSH through the
// reusable idcache module with a LD/ST QUEUE and STORE-TO-LOAD FORWARDING: a
// LOAD performs when its address is ready and no older unperformed memory op
// blocks it (a FLUSH, or a store with an unknown address); it forwards the data
// of the youngest older store to its address if there is one, else reads idc.
// Two memory slots work in parallel: the CACHE slot (oldest performable op
// needing idc: a ST/FLUSH at the head or a non-forwarding load) and the
// FORWARDING slot (oldest performable forwarding load). Tomasulo with a 4-entry
// re-order buffer, single dispatch, one ALU. For combinational equivalence
// checking against the Ivy-generated RTL (ooo_cpu_ref.il):
//
//     ./check_ooo_golden.sh ooo_cpu_ref ooo_fwd_golden.sv
//
// It extends ooo_lsq_golden.sv (stage 3b); the idcache/main_mem/ic/dc modules
// are those of dual_issue_golden.sv / cpu_gen_golden.sv (the same `idcache`
// module instance), with their reset lists completed (every scalar register
// resets under rst, address latches included, as ivy_to_rtl emits them).
//
// The register boundary matches the Ivy model exactly, register for register:
//
//   scalars   : pc, d_ir, d_valid, d_pred, d_pc, rob_head, rob_tail, ex_valid,
//               ex_idx, ex_ir, ex_a, ex_b (cpu); mbusy, mfa, mfi (idc.main_mem);
//               ifill_on/got/miss (idc.ic); dfill_on/got/miss (idc.dc) -- all
//               synchronously reset by `rst` to their `after init` value, else 0.
//   banks     : rob_a_K, rob_a_rdy_K, rob_b_K, rob_b_rdy_K (K = 0..3), updated
//               by the three result BROADCASTS (ALU result, cache load, forwarded load);
//               rob_busy_K and rat_valid_R (R = 0..7), cleared wholesale by the
//               SQUASH. One register per index; reset to 0 under rst.
//   memories  : rf, rat_idx, rob_ir, rob_pc, rob_pred, rob_take, rob_issued,
//               rob_done, rob_val, rob_a_src, rob_b_src (cpu); bp.bht;
//               idc.main_mem.real_mem (the program, injected for simulation),
//               idc.ic.icache, idc.dc.dcache -- point-written arrays with a
//               power-on $meminit, NOT reset by rst; `initial` blocks here.
//
// The cpu always-block is a line-by-line transcription of the Ivy clock action
// (ALU complete, cache-load perform, forwarded-load perform, broadcast, retire
// [+ ST/FLUSH at head, squash], issue, dispatch, fetch), which reads only
// pre-state values, so it transcribes to nonblocking assignments directly.
//
// Instruction encoding: [15:13] opcode [12:10] rd [9:7] ra [6:4] rb [7:0] imm.
// Opcodes: 0 NOP, 1 ADD, 2 SUB, 3 LI, 4 LD rd,[ra], 5 ST [ra],rb,
//          6 BEQZ ra,imm8, 7 FLUSH [ra].

module cpu ( \posedge , rst );
    input \posedge ;
    input rst;

    // ---- architectural state ----
    reg [7:0]  pc;
    reg [15:0] rf  [0:7];

    // ---- IF/ID latch ----
    reg [15:0] d_ir;
    reg        d_valid;
    reg        d_pred;              // predicted-taken bit carried with the instruction
    reg [7:0]  d_pc;                // the instruction's own pc

    // ---- rename table ----
    reg        rat_valid_0, rat_valid_1, rat_valid_2, rat_valid_3,
               rat_valid_4, rat_valid_5, rat_valid_6, rat_valid_7;   // bank (squash clears all)
    reg [1:0]  rat_idx   [0:7];

    // ---- re-order buffer ----
    reg [1:0]  rob_head;
    reg [1:0]  rob_tail;
    reg        rob_busy_0, rob_busy_1, rob_busy_2, rob_busy_3;       // bank (squash clears all)
    reg [15:0] rob_ir     [0:3];
    reg [7:0]  rob_pc     [0:3];
    reg        rob_pred   [0:3];
    reg        rob_take   [0:3];
    reg        rob_issued [0:3];
    reg        rob_done   [0:3];
    reg [15:0] rob_val    [0:3];
    reg [1:0]  rob_a_src  [0:3];
    reg [1:0]  rob_b_src  [0:3];
    // reservation-station operand banks (one register per ROB index)
    reg [15:0] rob_a_0, rob_a_1, rob_a_2, rob_a_3;
    reg        rob_a_rdy_0, rob_a_rdy_1, rob_a_rdy_2, rob_a_rdy_3;
    reg [15:0] rob_b_0, rob_b_1, rob_b_2, rob_b_3;
    reg        rob_b_rdy_0, rob_b_rdy_1, rob_b_rdy_2, rob_b_rdy_3;

    // ---- ALU latch ----
    reg        ex_valid;
    reg [1:0]  ex_idx;
    reg [15:0] ex_ir;
    reg [15:0] ex_a;
    reg [15:0] ex_b;

    // ---- power-on init of the memories (matches the Ivy `after init`;
    //      init-only, not part of the combinational check) ----
    integer ii;
    initial begin
        for (ii = 0; ii < 8; ii = ii + 1) rf[ii] = 16'd0;
        for (ii = 0; ii < 4; ii = ii + 1) begin rob_issued[ii] = 1'b0; rob_done[ii] = 1'b0; end
    end

    // ---- bank reads ----
    function [15:0] sel_a(input [1:0] i);
        case (i) 2'd0: sel_a = rob_a_0; 2'd1: sel_a = rob_a_1; 2'd2: sel_a = rob_a_2; default: sel_a = rob_a_3; endcase
    endfunction
    function [15:0] sel_b(input [1:0] i);
        case (i) 2'd0: sel_b = rob_b_0; 2'd1: sel_b = rob_b_1; 2'd2: sel_b = rob_b_2; default: sel_b = rob_b_3; endcase
    endfunction
    function sel_a_rdy(input [1:0] i);
        case (i) 2'd0: sel_a_rdy = rob_a_rdy_0; 2'd1: sel_a_rdy = rob_a_rdy_1; 2'd2: sel_a_rdy = rob_a_rdy_2; default: sel_a_rdy = rob_a_rdy_3; endcase
    endfunction
    function sel_b_rdy(input [1:0] i);
        case (i) 2'd0: sel_b_rdy = rob_b_rdy_0; 2'd1: sel_b_rdy = rob_b_rdy_1; 2'd2: sel_b_rdy = rob_b_rdy_2; default: sel_b_rdy = rob_b_rdy_3; endcase
    endfunction
    function sel_busy(input [1:0] i);
        case (i) 2'd0: sel_busy = rob_busy_0; 2'd1: sel_busy = rob_busy_1; 2'd2: sel_busy = rob_busy_2; default: sel_busy = rob_busy_3; endcase
    endfunction
    function sel_rat_valid(input [2:0] r);
        case (r)
            3'd0: sel_rat_valid = rat_valid_0; 3'd1: sel_rat_valid = rat_valid_1;
            3'd2: sel_rat_valid = rat_valid_2; 3'd3: sel_rat_valid = rat_valid_3;
            3'd4: sel_rat_valid = rat_valid_4; 3'd5: sel_rat_valid = rat_valid_5;
            3'd6: sel_rat_valid = rat_valid_6; default: sel_rat_valid = rat_valid_7;
        endcase
    endfunction
    function is_mem(input [2:0] op);
        is_mem = (op == 3'd4) | (op == 3'd5) | (op == 3'd7);
    endfunction

    // ---- ROB occupancy ----
    wire rob_full = sel_busy(rob_tail);

    // ---- dispatch decode ----
    wire [2:0] d_opcode = d_ir[15:13];
    wire [2:0] d_rd     = d_ir[12:10];
    wire [2:0] d_ra     = d_ir[9:7];
    wire [2:0] d_rb     = d_ir[6:4];
    wire [7:0] d_target = d_ir[7:0];
    wire d_wr      = (d_opcode == 3'd1) | (d_opcode == 3'd2) | (d_opcode == 3'd3) | (d_opcode == 3'd4);   // writes rd: renamed
    wire d_branch  = (d_opcode == 3'd6);
    wire d_exec    = (d_opcode == 3'd1) | (d_opcode == 3'd2) | (d_opcode == 3'd3) | (d_opcode == 3'd6);   // goes through the ALU
    wire d_mem     = is_mem(d_opcode);                                                                   // executes at the head
    wire d_needs_a = (d_opcode == 3'd1) | (d_opcode == 3'd2) | (d_opcode == 3'd4) | (d_opcode == 3'd5) | (d_opcode == 3'd6) | (d_opcode == 3'd7);
    wire d_needs_b = (d_opcode == 3'd1) | (d_opcode == 3'd2) | (d_opcode == 3'd5);

    // ---- retire decode ----
    wire [15:0] r_ir     = rob_ir[rob_head];
    wire [2:0]  r_opcode = r_ir[15:13];
    wire [2:0]  r_rd     = r_ir[12:10];
    wire [7:0]  r_target = r_ir[7:0];
    wire        r_wr     = (r_opcode == 3'd1) | (r_opcode == 3'd2) | (r_opcode == 3'd3) | (r_opcode == 3'd4);
    wire        r_branch = (r_opcode == 3'd6);
    wire        r_mem    = is_mem(r_opcode);
    wire [15:0] r_val    = rob_val[rob_head];
    wire        r_rat_clear = sel_rat_valid(r_rd) & (rat_idx[r_rd] == rob_head);
    wire [7:0]  r_pc     = rob_pc[rob_head];
    wire        r_take   = rob_take[rob_head];
    wire        r_pred   = rob_pred[rob_head];

    // ---- head-relative entry indices ----
    wire [1:0] h0 = rob_head;
    wire [1:0] h1 = rob_head + 2'd1;
    wire [1:0] h2 = rob_head + 2'd2;
    wire [1:0] h3 = rob_head + 2'd3;

    // ---- the LD/ST queue: per head-relative position j, an unperformed store
    // with a known address (a forwarding candidate; passable when the address
    // differs), a blocker (an unperformed FLUSH, or a store whose address is not
    // yet known), and an unperformed load with a known address ----
    wire [2:0] q0_op = rob_ir[h0][15:13];
    wire [2:0] q1_op = rob_ir[h1][15:13];
    wire [2:0] q2_op = rob_ir[h2][15:13];
    wire [2:0] q3_op = rob_ir[h3][15:13];
    wire [7:0] q0_addr = sel_a(h0);   wire [7:0] q1_addr = sel_a(h1);
    wire [7:0] q2_addr = sel_a(h2);   wire [7:0] q3_addr = sel_a(h3);
    wire q0_st  = sel_busy(h0) & ~rob_done[h0] & (q0_op == 3'd5) & sel_a_rdy(h0);
    wire q1_st  = sel_busy(h1) & ~rob_done[h1] & (q1_op == 3'd5) & sel_a_rdy(h1);
    wire q2_st  = sel_busy(h2) & ~rob_done[h2] & (q2_op == 3'd5) & sel_a_rdy(h2);
    wire q0_blk = sel_busy(h0) & ~rob_done[h0] & (((q0_op == 3'd5) & ~sel_a_rdy(h0)) | (q0_op == 3'd7));
    wire q1_blk = sel_busy(h1) & ~rob_done[h1] & (((q1_op == 3'd5) & ~sel_a_rdy(h1)) | (q1_op == 3'd7));
    wire q2_blk = sel_busy(h2) & ~rob_done[h2] & (((q2_op == 3'd5) & ~sel_a_rdy(h2)) | (q2_op == 3'd7));
    wire q0_ld  = sel_busy(h0) & ~rob_done[h0] & (q0_op == 3'd4) & sel_a_rdy(h0);
    wire q1_ld  = sel_busy(h1) & ~rob_done[h1] & (q1_op == 3'd4) & sel_a_rdy(h1);
    wire q2_ld  = sel_busy(h2) & ~rob_done[h2] & (q2_op == 3'd4) & sel_a_rdy(h2);
    wire q3_ld  = sel_busy(h3) & ~rob_done[h3] & (q3_op == 3'd4) & sel_a_rdy(h3);

    // ---- store-to-load forwarding source for the load at position i: the
    // youngest older unperformed store with a known address equal to the load's ----
    wire f1_m0 = q0_st & (q0_addr == q1_addr);
    wire f2_m1 = q1_st & (q1_addr == q2_addr);
    wire f2_m0 = q0_st & (q0_addr == q2_addr);
    wire f3_m2 = q2_st & (q2_addr == q3_addr);
    wire f3_m1 = q1_st & (q1_addr == q3_addr);
    wire f3_m0 = q0_st & (q0_addr == q3_addr);
    wire fwd1 = f1_m0;                    wire [1:0] fsrc1 = h0;
    wire fwd2 = f2_m1 | f2_m0;            wire [1:0] fsrc2 = f2_m1 ? h1 : h0;
    wire fwd3 = f3_m2 | f3_m1 | f3_m0;    wire [1:0] fsrc3 = f3_m2 ? h2 : f3_m1 ? h1 : h0;

    // ---- performable memory ops: a load with a known address, no older blocker,
    // and (if forwarding) its source's data ready; a ST/FLUSH only at the head ----
    wire ldok0 = q0_ld;
    wire ldok1 = q1_ld & ~q0_blk & (~fwd1 | sel_b_rdy(fsrc1));
    wire ldok2 = q2_ld & ~q0_blk & ~q1_blk & (~fwd2 | sel_b_rdy(fsrc2));
    wire ldok3 = q3_ld & ~q0_blk & ~q1_blk & ~q2_blk & (~fwd3 | sel_b_rdy(fsrc3));
    wire stok0 = sel_busy(h0) & ~rob_done[h0] & ((q0_op == 3'd5) | (q0_op == 3'd7)) & sel_a_rdy(h0) & sel_b_rdy(h0);

    // ---- the CACHE slot: the oldest performable op that needs idc ----
    wire c0 = ldok0 | stok0;
    wire c1 = ldok1 & ~fwd1;
    wire c2 = ldok2 & ~fwd2;
    wire c3 = ldok3 & ~fwd3;
    wire mem_valid = c0 | c1 | c2 | c3;
    wire [1:0]  mem_sel    = c0 ? h0 : c1 ? h1 : c2 ? h2 : h3;
    wire [15:0] mem_ir     = rob_ir[mem_sel];
    wire [2:0]  mem_opcode = mem_ir[15:13];
    wire        mem_is_load = (mem_opcode == 3'd4);
    wire [15:0] mem_a      = sel_a(mem_sel);                 // its operands (address / store data)
    wire [15:0] mem_b      = sel_b(mem_sel);
    wire [7:0]  mem_addr   = mem_a[7:0];
    wire        mem_ready  = mem_valid;                      // the request to idc
    wire        idc_data_stall;
    wire [15:0] idc_read_data;
    wire        mem_perform = mem_valid & ~idc_data_stall;      // the op performs if idc does not stall
    wire        ld_perform  = mem_perform & mem_is_load;        // a cache load performs
    wire        mem_retire  = mem_perform & ~mem_is_load;       // a ST/FLUSH performs at the head: it retires now
    wire        retire      = (sel_busy(rob_head) & rob_done[rob_head]) | mem_retire;

    // ---- the FORWARDING slot: the oldest performable forwarding load ----
    wire w1 = ldok1 & fwd1;
    wire w2 = ldok2 & fwd2;
    wire w3 = ldok3 & fwd3;
    wire        fwd_perform = w1 | w2 | w3;
    wire [1:0]  fwd_sel  = w1 ? h1 : w2 ? h2 : h3;
    wire [1:0]  fwd_src  = w1 ? fsrc1 : w2 ? fsrc2 : fsrc3;
    wire [15:0] fwd_data = sel_b(fwd_src);
    // a retiring BEQZ whose outcome differs from its prediction: squash
    wire        squash   = retire & r_branch & (r_take != r_pred);
    wire [7:0]  redirect_pc = r_take ? r_target : (r_pc + 8'd1);

    // ---- a FLUSH in flight (IF/ID or ROB) stalls fetch until it retires ----
    wire flush_pending = (d_valid & (d_opcode == 3'd7))
                       | (rob_busy_0 & (rob_ir[0][15:13] == 3'd7))
                       | (rob_busy_1 & (rob_ir[1][15:13] == 3'd7))
                       | (rob_busy_2 & (rob_ir[2][15:13] == 3'd7))
                       | (rob_busy_3 & (rob_ir[3][15:13] == 3'd7));

    wire dispatch     = d_valid & ~rob_full & ~squash;
    wire if_stall     = d_valid & rob_full;
    wire fetch_active = ~if_stall & ~squash & ~flush_pending;    // IF presents the pc to idc
    wire idc_fetch_valid0;
    wire [15:0] idc_fetch_data0;
    wire fetch_en     = fetch_active & idc_fetch_valid0;         // ... and latches the word if idc returns it

    // ---- ALU ----
    wire [2:0] ex_opcode = ex_ir[15:13];
    wire [7:0] ex_target = ex_ir[7:0];
    wire [15:0] ex_res = (ex_opcode == 3'd1) ? (ex_a + ex_b) :
                         (ex_opcode == 3'd2) ? (ex_a - ex_b) :
                         (ex_opcode == 3'd3) ? {8'd0, ex_target} : 16'd0;
    wire ex_take = (ex_opcode == 3'd6) & (ex_a == 16'd0);       // the true BEQZ outcome

    // ---- operand capture at dispatch (rf / ROB / ALU bus / cache load / forwarded load) ----
    wire [1:0]  d_a_idx = rat_idx[d_ra];
    wire        d_a_bus = ex_valid & (ex_idx == d_a_idx);
    wire        d_a_ld  = ld_perform & (d_a_idx == mem_sel);
    wire        d_a_fw  = fwd_perform & (d_a_idx == fwd_sel);
    wire        d_a_rdy = ~d_needs_a | ~sel_rat_valid(d_ra) | rob_done[d_a_idx] | d_a_bus | d_a_ld | d_a_fw;
    wire [15:0] d_a_val = ~sel_rat_valid(d_ra) ? rf[d_ra] :
                          d_a_bus ? ex_res : d_a_ld ? idc_read_data : d_a_fw ? fwd_data : rob_val[d_a_idx];

    wire [1:0]  d_b_idx = rat_idx[d_rb];
    wire        d_b_bus = ex_valid & (ex_idx == d_b_idx);
    wire        d_b_ld  = ld_perform & (d_b_idx == mem_sel);
    wire        d_b_fw  = fwd_perform & (d_b_idx == fwd_sel);
    wire        d_b_rdy = ~d_needs_b | ~sel_rat_valid(d_rb) | rob_done[d_b_idx] | d_b_bus | d_b_ld | d_b_fw;
    wire [15:0] d_b_val = ~sel_rat_valid(d_rb) ? rf[d_rb] :
                          d_b_bus ? ex_res : d_b_ld ? idc_read_data : d_b_fw ? fwd_data : rob_val[d_b_idx];

    // ---- issue selection: oldest ready, un-issued ALU/BEQZ entry (never a memory op) ----
    wire rdy0 = sel_busy(h0) & ~rob_issued[h0] & sel_a_rdy(h0) & sel_b_rdy(h0) & ~is_mem(rob_ir[h0][15:13]);
    wire rdy1 = sel_busy(h1) & ~rob_issued[h1] & sel_a_rdy(h1) & sel_b_rdy(h1) & ~is_mem(rob_ir[h1][15:13]);
    wire rdy2 = sel_busy(h2) & ~rob_issued[h2] & sel_a_rdy(h2) & sel_b_rdy(h2) & ~is_mem(rob_ir[h2][15:13]);
    wire rdy3 = sel_busy(h3) & ~rob_issued[h3] & sel_a_rdy(h3) & sel_b_rdy(h3) & ~is_mem(rob_ir[h3][15:13]);
    wire issue = ~squash & (rdy0 | rdy1 | rdy2 | rdy3);
    wire [1:0] issue_idx = rdy0 ? h0 : rdy1 ? h1 : rdy2 ? h2 : h3;

    // ---- operands of the issuing entry (as wires: no function calls in the always block) ----
    wire [15:0] issue_a = sel_a(issue_idx);
    wire [15:0] issue_b = sel_b(issue_idx);

    // ---- the branch predictor: predict at fetch, train at retire ----
    wire bp_predicted_taken;
    bp bp (
        .\posedge (\posedge ), .rst(rst),
        .fetch_pc(pc), .br_valid(retire & r_branch), .br_pc(r_pc), .br_taken(r_take),
        .predicted_taken(bp_predicted_taken)
    );

    // ---- the memory subsystem: the idcache module ----
    // Fetch port: the pc whenever IF is really fetching. Data port: the cache
    // slot's op (one request kind at a time).
    wire [15:0] idc_fetch_data1_unused;
    wire        idc_fetch_valid1_unused;
    idcache idc (
        .\posedge (\posedge ), .rst(rst),
        .fetch_req(fetch_active), .fetch_addr(pc),
        .read_req(mem_ready & (mem_opcode == 3'd4)),
        .write_req(mem_ready & (mem_opcode == 3'd5)),
        .flush_req(mem_ready & (mem_opcode == 3'd7)),
        .data_addr(mem_addr), .write_data(mem_b),
        .fetch_data0(idc_fetch_data0), .fetch_valid0(idc_fetch_valid0),
        .fetch_data1(idc_fetch_data1_unused), .fetch_valid1(idc_fetch_valid1_unused),
        .read_data(idc_read_data), .data_stall(idc_data_stall)
    );

    // ---- fetch and prediction ----
    wire [15:0] fetched = idc_fetch_data0;
    wire        f_is_branch = (fetched[15:13] == 3'd6);
    wire        f_ptaken    = f_is_branch & bp_predicted_taken;
    wire [7:0]  f_target    = fetched[7:0];
    wire [7:0]  pred_next_pc = f_ptaken ? f_target : (pc + 8'd1);

    // ---- broadcast hits, per bank element: the ALU result (ex_idx), the cache
    //      load's word (mem_sel) and the forwarded data (fwd_sel) ----
    wire hx_a0 = ex_valid & rob_busy_0 & (rob_a_src[0] == ex_idx);   wire hl_a0 = ld_perform & rob_busy_0 & (rob_a_src[0] == mem_sel);   wire hf_a0 = fwd_perform & rob_busy_0 & (rob_a_src[0] == fwd_sel);
    wire hx_a1 = ex_valid & rob_busy_1 & (rob_a_src[1] == ex_idx);   wire hl_a1 = ld_perform & rob_busy_1 & (rob_a_src[1] == mem_sel);   wire hf_a1 = fwd_perform & rob_busy_1 & (rob_a_src[1] == fwd_sel);
    wire hx_a2 = ex_valid & rob_busy_2 & (rob_a_src[2] == ex_idx);   wire hl_a2 = ld_perform & rob_busy_2 & (rob_a_src[2] == mem_sel);   wire hf_a2 = fwd_perform & rob_busy_2 & (rob_a_src[2] == fwd_sel);
    wire hx_a3 = ex_valid & rob_busy_3 & (rob_a_src[3] == ex_idx);   wire hl_a3 = ld_perform & rob_busy_3 & (rob_a_src[3] == mem_sel);   wire hf_a3 = fwd_perform & rob_busy_3 & (rob_a_src[3] == fwd_sel);
    wire hx_b0 = ex_valid & rob_busy_0 & (rob_b_src[0] == ex_idx);   wire hl_b0 = ld_perform & rob_busy_0 & (rob_b_src[0] == mem_sel);   wire hf_b0 = fwd_perform & rob_busy_0 & (rob_b_src[0] == fwd_sel);
    wire hx_b1 = ex_valid & rob_busy_1 & (rob_b_src[1] == ex_idx);   wire hl_b1 = ld_perform & rob_busy_1 & (rob_b_src[1] == mem_sel);   wire hf_b1 = fwd_perform & rob_busy_1 & (rob_b_src[1] == fwd_sel);
    wire hx_b2 = ex_valid & rob_busy_2 & (rob_b_src[2] == ex_idx);   wire hl_b2 = ld_perform & rob_busy_2 & (rob_b_src[2] == mem_sel);   wire hf_b2 = fwd_perform & rob_busy_2 & (rob_b_src[2] == fwd_sel);
    wire hx_b3 = ex_valid & rob_busy_3 & (rob_b_src[3] == ex_idx);   wire hl_b3 = ld_perform & rob_busy_3 & (rob_b_src[3] == mem_sel);   wire hf_b3 = fwd_perform & rob_busy_3 & (rob_b_src[3] == fwd_sel);

    always @(posedge \posedge ) begin
        // ---- complete: write the ALU result (and branch outcome) ----
        if (ex_valid) begin
            rob_val[ex_idx]  <= ex_res;
            rob_done[ex_idx] <= 1'b1;
            rob_take[ex_idx] <= ex_take;
        end
        // ---- perform loads: the cache slot's gets idc's word, the forwarding
        //      slot's its source store's data ----
        if (ld_perform) begin
            rob_val[mem_sel]  <= idc_read_data;
            rob_done[mem_sel] <= 1'b1;
        end
        if (fwd_perform) begin
            rob_val[fwd_sel]  <= fwd_data;
            rob_done[fwd_sel] <= 1'b1;
        end

        // ---- broadcast: ALU result to entries waiting on ex_idx, cache load's word
        //      to those waiting on mem_sel, forwarded data to those waiting on fwd_sel
        //      (a waiting operand is not ready) ----
        if (hx_a0 & ~rob_a_rdy_0) rob_a_0 <= ex_res; else if (hl_a0 & ~rob_a_rdy_0) rob_a_0 <= idc_read_data; else if (hf_a0 & ~rob_a_rdy_0) rob_a_0 <= fwd_data;
        if (hx_a1 & ~rob_a_rdy_1) rob_a_1 <= ex_res; else if (hl_a1 & ~rob_a_rdy_1) rob_a_1 <= idc_read_data; else if (hf_a1 & ~rob_a_rdy_1) rob_a_1 <= fwd_data;
        if (hx_a2 & ~rob_a_rdy_2) rob_a_2 <= ex_res; else if (hl_a2 & ~rob_a_rdy_2) rob_a_2 <= idc_read_data; else if (hf_a2 & ~rob_a_rdy_2) rob_a_2 <= fwd_data;
        if (hx_a3 & ~rob_a_rdy_3) rob_a_3 <= ex_res; else if (hl_a3 & ~rob_a_rdy_3) rob_a_3 <= idc_read_data; else if (hf_a3 & ~rob_a_rdy_3) rob_a_3 <= fwd_data;
        if (hx_b0 & ~rob_b_rdy_0) rob_b_0 <= ex_res; else if (hl_b0 & ~rob_b_rdy_0) rob_b_0 <= idc_read_data; else if (hf_b0 & ~rob_b_rdy_0) rob_b_0 <= fwd_data;
        if (hx_b1 & ~rob_b_rdy_1) rob_b_1 <= ex_res; else if (hl_b1 & ~rob_b_rdy_1) rob_b_1 <= idc_read_data; else if (hf_b1 & ~rob_b_rdy_1) rob_b_1 <= fwd_data;
        if (hx_b2 & ~rob_b_rdy_2) rob_b_2 <= ex_res; else if (hl_b2 & ~rob_b_rdy_2) rob_b_2 <= idc_read_data; else if (hf_b2 & ~rob_b_rdy_2) rob_b_2 <= fwd_data;
        if (hx_b3 & ~rob_b_rdy_3) rob_b_3 <= ex_res; else if (hl_b3 & ~rob_b_rdy_3) rob_b_3 <= idc_read_data; else if (hf_b3 & ~rob_b_rdy_3) rob_b_3 <= fwd_data;
        if (hx_a0 | hl_a0 | hf_a0) rob_a_rdy_0 <= 1'b1;   if (hx_b0 | hl_b0 | hf_b0) rob_b_rdy_0 <= 1'b1;
        if (hx_a1 | hl_a1 | hf_a1) rob_a_rdy_1 <= 1'b1;   if (hx_b1 | hl_b1 | hf_b1) rob_b_rdy_1 <= 1'b1;
        if (hx_a2 | hl_a2 | hf_a2) rob_a_rdy_2 <= 1'b1;   if (hx_b2 | hl_b2 | hf_b2) rob_b_rdy_2 <= 1'b1;
        if (hx_a3 | hl_a3 | hf_a3) rob_a_rdy_3 <= 1'b1;   if (hx_b3 | hl_b3 | hf_b3) rob_b_rdy_3 <= 1'b1;

        // ---- retire the head: a done ALU/BEQZ/NOP/LD entry, or a ST/FLUSH idc serves
        //      this cycle; a mispredicted BEQZ squashes everything behind it ----
        if (retire) begin
            if (r_wr) rf[r_rd] <= r_val;
            if (r_rat_clear) begin
                case (r_rd)
                    3'd0: rat_valid_0 <= 1'b0; 3'd1: rat_valid_1 <= 1'b0;
                    3'd2: rat_valid_2 <= 1'b0; 3'd3: rat_valid_3 <= 1'b0;
                    3'd4: rat_valid_4 <= 1'b0; 3'd5: rat_valid_5 <= 1'b0;
                    3'd6: rat_valid_6 <= 1'b0; default: rat_valid_7 <= 1'b0;
                endcase
            end
            case (rob_head)
                2'd0: rob_busy_0 <= 1'b0; 2'd1: rob_busy_1 <= 1'b0;
                2'd2: rob_busy_2 <= 1'b0; default: rob_busy_3 <= 1'b0;
            endcase
            if (squash) begin
                rob_busy_0 <= 1'b0; rob_busy_1 <= 1'b0; rob_busy_2 <= 1'b0; rob_busy_3 <= 1'b0;
                rat_valid_0 <= 1'b0; rat_valid_1 <= 1'b0; rat_valid_2 <= 1'b0; rat_valid_3 <= 1'b0;
                rat_valid_4 <= 1'b0; rat_valid_5 <= 1'b0; rat_valid_6 <= 1'b0; rat_valid_7 <= 1'b0;
                rob_tail <= rob_head + 2'd1;        // empty ROB (pre-state head)
                ex_valid <= 1'b0;                    // kill the in-flight ALU op
                d_valid  <= 1'b0;                    // kill the fetched instruction
                pc       <= redirect_pc;
            end
            rob_head <= rob_head + 2'd1;
        end

        // ---- issue the oldest ready entry to the ALU ----
        if (issue) begin
            ex_valid <= 1'b1;
            ex_idx   <= issue_idx;
            ex_ir    <= rob_ir[issue_idx];
            ex_a     <= issue_a;
            ex_b     <= issue_b;
            rob_issued[issue_idx] <= 1'b1;
        end else begin
            ex_valid <= 1'b0;
        end

        // ---- dispatch: allocate the tail entry, rename, capture operands; the
        //      IF/ID latch empties unless the fetch below refills it ----
        if (dispatch) begin
            case (rob_tail)
                2'd0: begin rob_busy_0 <= 1'b1; rob_a_0 <= d_a_val; rob_a_rdy_0 <= d_a_rdy; rob_b_0 <= d_b_val; rob_b_rdy_0 <= d_b_rdy; end
                2'd1: begin rob_busy_1 <= 1'b1; rob_a_1 <= d_a_val; rob_a_rdy_1 <= d_a_rdy; rob_b_1 <= d_b_val; rob_b_rdy_1 <= d_b_rdy; end
                2'd2: begin rob_busy_2 <= 1'b1; rob_a_2 <= d_a_val; rob_a_rdy_2 <= d_a_rdy; rob_b_2 <= d_b_val; rob_b_rdy_2 <= d_b_rdy; end
                default: begin rob_busy_3 <= 1'b1; rob_a_3 <= d_a_val; rob_a_rdy_3 <= d_a_rdy; rob_b_3 <= d_b_val; rob_b_rdy_3 <= d_b_rdy; end
            endcase
            rob_ir[rob_tail]     <= d_ir;
            rob_pc[rob_tail]     <= d_pc;
            rob_pred[rob_tail]   <= d_pred;
            rob_issued[rob_tail] <= ~d_exec & ~d_mem;   // NOP: issued+done at once; ALU/BEQZ: issues
            rob_done[rob_tail]   <= ~d_exec & ~d_mem;   // later; memory op: neither until it performs
            rob_val[rob_tail]    <= 16'd0;
            rob_a_src[rob_tail]  <= d_a_idx;
            rob_b_src[rob_tail]  <= d_b_idx;
            if (d_wr) begin
                case (d_rd)
                    3'd0: rat_valid_0 <= 1'b1; 3'd1: rat_valid_1 <= 1'b1;
                    3'd2: rat_valid_2 <= 1'b1; 3'd3: rat_valid_3 <= 1'b1;
                    3'd4: rat_valid_4 <= 1'b1; 3'd5: rat_valid_5 <= 1'b1;
                    3'd6: rat_valid_6 <= 1'b1; default: rat_valid_7 <= 1'b1;
                endcase
                rat_idx[d_rd] <= rob_tail;
            end
            rob_tail <= rob_tail + 2'd1;
            d_valid  <= 1'b0;
        end

        // ---- fetch along the predicted path when IF is active and idc returns the word ----
        if (fetch_en) begin
            d_ir    <= fetched;
            d_valid <= 1'b1;
            d_pred  <= f_ptaken;
            d_pc    <= pc;
            pc      <= pred_next_pc;
        end

        // ---- synchronous reset of every scalar/bank register (the Ivy
        //      `after init` values; registers it does not mention reset to 0,
        //      as ivy_to_rtl emits them). Memories are not reset. ----
        if (rst) begin
            pc <= 8'd0; d_ir <= 16'd0; d_valid <= 1'b0; d_pred <= 1'b0; d_pc <= 8'd0;
            rob_head <= 2'd0; rob_tail <= 2'd0;
            ex_valid <= 1'b0; ex_idx <= 2'd0; ex_ir <= 16'd0; ex_a <= 16'd0; ex_b <= 16'd0;
            rob_busy_0 <= 1'b0; rob_busy_1 <= 1'b0; rob_busy_2 <= 1'b0; rob_busy_3 <= 1'b0;
            rat_valid_0 <= 1'b0; rat_valid_1 <= 1'b0; rat_valid_2 <= 1'b0; rat_valid_3 <= 1'b0;
            rat_valid_4 <= 1'b0; rat_valid_5 <= 1'b0; rat_valid_6 <= 1'b0; rat_valid_7 <= 1'b0;
            rob_a_0 <= 16'd0; rob_a_1 <= 16'd0; rob_a_2 <= 16'd0; rob_a_3 <= 16'd0;
            rob_b_0 <= 16'd0; rob_b_1 <= 16'd0; rob_b_2 <= 16'd0; rob_b_3 <= 16'd0;
            rob_a_rdy_0 <= 1'b0; rob_a_rdy_1 <= 1'b0; rob_a_rdy_2 <= 1'b0; rob_a_rdy_3 <= 1'b0;
            rob_b_rdy_0 <= 1'b0; rob_b_rdy_1 <= 1'b0; rob_b_rdy_2 <= 1'b0; rob_b_rdy_3 <= 1'b0;
        end
    end
endmodule

// ===========================================================================
// bp: bimodal branch predictor (16-entry table of 2-bit saturating counters),
// identical to the one in 5stage_bp_cpu_ref / dual_issue_golden. Its table
// bht is a memory (power-on init 1 = weakly not-taken, not reset by rst).
// ===========================================================================
module bp ( \posedge , rst, fetch_pc, br_valid, br_pc, br_taken, predicted_taken );
    input \posedge ; input rst;
    input [7:0] fetch_pc; input br_valid; input [7:0] br_pc; input br_taken;
    output predicted_taken;

    reg [1:0] bht [0:15];
    integer bi;
    initial for (bi = 0; bi < 16; bi = bi + 1) bht[bi] = 2'd1;   // weakly not-taken
    wire [3:0] pred_idx = fetch_pc[3:0];
    wire [3:0] upd_idx  = br_pc[3:0];
    assign predicted_taken = (bht[pred_idx]==2'd2) | (bht[pred_idx]==2'd3);

    always @(posedge \posedge ) begin
        if (br_valid) begin
            if (br_taken) begin
                if (bht[upd_idx] != 2'd3) bht[upd_idx] <= bht[upd_idx] + 2'd1;
            end else begin
                if (bht[upd_idx] != 2'd0) bht[upd_idx] <= bht[upd_idx] - 2'd1;
            end
        end
    end
endmodule

// ===========================================================================
// idcache: the reusable I/D-cache + main-memory module (main_mem + ic + dc),
// as in dual_issue_golden.sv / cpu_gen_golden.sv. The proof-only interface
// isolates (mem_ic/mem_dc and their props) hold no RTL state and are omitted.
// Bit layouts:
//   icline (36): [35] full | [34:32] tag | [31:16] word1 | [15:0] word0
//   dcline (40): [39] full | [38] d1 | [37] d0 | [36:34] tag | [33:18] w1
//                | [17:2] w0 | [1:0] (unused 0)
//   addr (8):    [7:5] tag | [4:1] index | [0] wsel
// ===========================================================================
module idcache (
    \posedge , rst,
    fetch_req, fetch_addr, read_req, write_req, flush_req, data_addr, write_data,
    fetch_data0, fetch_valid0, fetch_data1, fetch_valid1, read_data, data_stall
);
    input \posedge ; input rst;
    input        fetch_req;
    input [7:0]  fetch_addr;
    input        read_req;
    input        write_req;
    input        flush_req;
    input [7:0]  data_addr;
    input [15:0] write_data;
    output [15:0] fetch_data0;
    output        fetch_valid0;
    output [15:0] fetch_data1;
    output        fetch_valid1;
    output [15:0] read_data;
    output        data_stall;

    // ---- inter-block wires ----
    wire [15:0] mm_ifill_data, mm_dfill_data;
    wire        mm_ifill_data_valid, mm_dfill_data_valid;
    wire [7:0]  ic_ifill_addr;
    wire        ic_ifill_addr_valid, ic_ifill_busy;
    wire [7:0]  dc_dfill_addr, dc_wb_word_addr;
    wire [15:0] dc_wb_word_data;
    wire        dc_dfill_req, dc_dfill_busy, dc_dmem_stall, dc_wb_en, dc_wb_word_en;
    wire        dc_wb_wsel_unused;

    assign data_stall = dc_dmem_stall | dc_wb_en;

    main_mem main_mem (
        .\posedge (\posedge ), .rst(rst),
        .ifill_addr(ic_ifill_addr),  .ifill_req(ic_ifill_addr_valid),
        .dfill_addr(dc_dfill_addr),  .dfill_req(dc_dfill_req),
        .dwrite_en(dc_wb_word_en),   .dwrite_addr(dc_wb_word_addr), .dwrite_data(dc_wb_word_data),
        .ifill_data(mm_ifill_data),  .ifill_data_valid(mm_ifill_data_valid),
        .dfill_data(mm_dfill_data),  .dfill_data_valid(mm_dfill_data_valid)
    );

    ic ic (
        .\posedge (\posedge ), .rst(rst),
        .fetch_addr(fetch_addr),  .fetch_addr_valid(fetch_req),
        .ifill_data(mm_ifill_data), .ifill_data_valid(mm_ifill_data_valid),
        .flush_addr(data_addr),   .flush_valid(flush_req & ~data_stall),
        .fetch_data(fetch_data0), .fetch_valid(fetch_valid0),
        .fetch_data1(fetch_data1), .fetch_valid1(fetch_valid1),
        .ifill_addr(ic_ifill_addr), .ifill_addr_valid(ic_ifill_addr_valid), .ifill_busy(ic_ifill_busy)
    );

    dc dc (
        .\posedge (\posedge ), .rst(rst),
        .req_addr(data_addr), .is_ld(read_req), .is_st(write_req), .is_flush(flush_req),
        .st_data(write_data),
        .dfill_data(mm_dfill_data), .dfill_data_valid(mm_dfill_data_valid),
        .ld_data(read_data), .dmem_stall(dc_dmem_stall),
        .dfill_addr(dc_dfill_addr), .dfill_req(dc_dfill_req), .dfill_busy(dc_dfill_busy),
        .wb_en(dc_wb_en), .wb_word_en(dc_wb_word_en), .wb_wsel(dc_wb_wsel_unused),
        .wb_word_addr(dc_wb_word_addr), .wb_word_data(dc_wb_word_data)
    );
endmodule

// ===========================================================================
// main memory: two-cycle read/fill port (D-priority) + single-cycle write port.
// ===========================================================================
module main_mem (
    \posedge , rst,
    ifill_addr, ifill_req, dfill_addr, dfill_req, dwrite_en, dwrite_addr, dwrite_data,
    ifill_data, ifill_data_valid, dfill_data, dfill_data_valid
);
    input \posedge ; input rst;
    input [7:0]  ifill_addr; input ifill_req;
    input [7:0]  dfill_addr; input dfill_req;
    input        dwrite_en; input [7:0] dwrite_addr; input [15:0] dwrite_data;
    output [15:0] ifill_data; output ifill_data_valid;
    output [15:0] dfill_data; output dfill_data_valid;

    reg [15:0] real_mem [0:255];
    reg        mbusy;
    reg [7:0]  mfa;
    reg        mfi;

    initial begin mbusy = 1'b0; mfi = 1'b0; end   // real_mem = program (injected)

    assign ifill_data       = real_mem[mfa];
    assign ifill_data_valid = mbusy & mfi;
    assign dfill_data       = real_mem[mfa];
    assign dfill_data_valid = mbusy & ~mfi;

    always @(posedge \posedge ) begin
        if (dwrite_en) real_mem[dwrite_addr] <= dwrite_data;
        if (mbusy) mbusy <= 1'b0;
        else if (dfill_req) begin mbusy <= 1'b1; mfi <= 1'b0; mfa <= dfill_addr; end
        else if (ifill_req) begin mbusy <= 1'b1; mfi <= 1'b1; mfa <= ifill_addr; end
        if (rst) begin mbusy <= 1'b0; mfi <= 1'b0; mfa <= 8'd0; end   // synchronous reset (all scalars)
    end
endmodule

// ===========================================================================
// instruction cache: read-only, two-word lines, two-cycle fill. Exports both
// the lane-0 fetch word and the lane-1 (odd sibling) word of the same line.
// ===========================================================================
module ic (
    \posedge , rst,
    fetch_addr, fetch_addr_valid, ifill_data, ifill_data_valid, flush_addr, flush_valid,
    fetch_data, fetch_valid, fetch_data1, fetch_valid1, ifill_addr, ifill_addr_valid, ifill_busy
);
    input \posedge ; input rst;
    input [7:0]  fetch_addr; input fetch_addr_valid;
    input [15:0] ifill_data; input ifill_data_valid;
    input [7:0]  flush_addr; input flush_valid;
    output [15:0] fetch_data; output fetch_valid;
    output [15:0] fetch_data1; output fetch_valid1;
    output [7:0]  ifill_addr; output ifill_addr_valid; output ifill_busy;

    reg [35:0] icache [0:15];
    reg        ifill_on;
    reg        ifill_got;
    reg [7:0]  ifill_miss;

    integer ii;
    initial begin ifill_on = 1'b0; ifill_got = 1'b0;
        for (ii = 0; ii < 16; ii = ii + 1) icache[ii] = 36'd0; end

    wire [7:0]  sib = (ifill_miss[0]==1'b0) ? (ifill_miss + 8'd1) : (ifill_miss - 8'd1);

    wire [3:0]  f_index = fetch_addr[4:1];
    wire        f_wsel  = fetch_addr[0];
    wire [35:0] f_iline = icache[f_index];
    wire f_full_hit = (f_iline[35]==1'b1) & (f_iline[34:32] == fetch_addr[7:5]);
    wire f_fill_hit = ifill_got & (fetch_addr == ifill_miss);
    wire f_arr_hit  = f_full_hit | f_fill_hit;
    wire [15:0] f_cword = (f_wsel==1'b0) ? f_iline[15:0] : f_iline[31:16];
    wire f_bypass = ifill_on & ifill_data_valid & (ifill_addr == fetch_addr)
                    & ~(flush_valid & (flush_addr == ifill_addr));

    assign fetch_valid = f_arr_hit | f_bypass;
    assign fetch_data  = f_arr_hit ? f_cword : ifill_data;

    // ---- lane 1: the odd sibling word (fetch_addr + 1) of the same line ----
    wire [7:0]  fetch_addr1 = fetch_addr + 8'd1;
    wire f_fill_hit1 = ifill_got & (fetch_addr1 == ifill_miss);
    wire f_arr_hit1  = f_full_hit | f_fill_hit1;
    wire [15:0] f_cword1 = f_iline[31:16];
    wire f_bypass1 = ifill_on & ifill_data_valid & (ifill_addr == fetch_addr1)
                     & ~(flush_valid & (flush_addr == ifill_addr));
    assign fetch_valid1 = (f_wsel==1'b0) & (f_arr_hit1 | f_bypass1);
    assign fetch_data1  = f_arr_hit1 ? f_cword1 : ifill_data;

    assign ifill_addr = (~ifill_on & ~ifill_got) ? fetch_addr
                      : (~ifill_got ? ifill_miss : sib);
    assign ifill_addr_valid = ifill_on | ifill_got | (fetch_addr_valid & ~fetch_valid);
    assign ifill_busy = ifill_on | ifill_got;

    wire [3:0]  fl_index = flush_addr[4:1];
    wire [35:0] fl_iline = icache[fl_index];
    wire fl_ihit = (fl_iline[35]==1'b1) & (fl_iline[34:32] == flush_addr[7:5]);

    always @(posedge \posedge ) begin
        if (ifill_on & ifill_data_valid & ~flush_valid) begin
            if (~ifill_got) begin
                if (ifill_miss[0]==1'b0)
                    icache[ifill_miss[4:1]] <= {1'b0, ifill_miss[7:5], 16'd0, ifill_data};
                else
                    icache[ifill_miss[4:1]] <= {1'b0, ifill_miss[7:5], ifill_data, 16'd0};
                ifill_on <= 1'b0; ifill_got <= 1'b1;
            end else begin
                if (sib[0]==1'b0)
                    icache[sib[4:1]] <= {1'b1, sib[7:5], icache[sib[4:1]][31:16], ifill_data};
                else
                    icache[sib[4:1]] <= {1'b1, sib[7:5], ifill_data, icache[sib[4:1]][15:0]};
                ifill_on <= 1'b0; ifill_got <= 1'b0;
            end
        end else if (~ifill_on & ifill_got) begin
            ifill_on <= 1'b1;
        end else if (~ifill_busy & fetch_addr_valid & ~fetch_valid) begin
            ifill_on <= 1'b1; ifill_got <= 1'b0; ifill_miss <= fetch_addr;
        end
        if (flush_valid & fl_ihit) icache[fl_index] <= 36'd0;
        if (flush_valid & (flush_addr == ifill_miss)) begin
            ifill_on <= 1'b0; ifill_got <= 1'b0;
        end
        if (rst) begin ifill_on <= 1'b0; ifill_got <= 1'b0; ifill_miss <= 8'd0; end   // synchronous reset (all scalars)
    end
endmodule

// ===========================================================================
// data cache: write-back, write-allocate, two-word lines, per-word dirty bit.
// ===========================================================================
module dc (
    \posedge , rst,
    req_addr, is_ld, is_st, is_flush, st_data, dfill_data, dfill_data_valid,
    ld_data, dmem_stall, dfill_addr, dfill_req, dfill_busy,
    wb_en, wb_word_en, wb_wsel, wb_word_addr, wb_word_data
);
    input \posedge ; input rst;
    input [7:0]  req_addr; input is_ld; input is_st; input is_flush;
    input [15:0] st_data;
    input [15:0] dfill_data; input dfill_data_valid;
    output [15:0] ld_data; output dmem_stall;
    output [7:0]  dfill_addr; output dfill_req; output dfill_busy;
    output        wb_en; output wb_word_en; output wb_wsel;
    output [7:0]  wb_word_addr; output [15:0] wb_word_data;

    reg [39:0] dcache [0:15];
    reg        dfill_on;
    reg        dfill_got;
    reg [7:0]  dfill_miss;

    integer di;
    initial begin dfill_on = 1'b0; dfill_got = 1'b0;
        for (di = 0; di < 16; di = di + 1) dcache[di] = 40'd0; end

    wire [3:0]  d_index = req_addr[4:1];
    wire        d_wsel  = req_addr[0];
    wire [39:0] d_line  = dcache[d_index];
    wire d_full   = (d_line[39]==1'b1);
    wire d_hit    = d_full & (d_line[36:34] == req_addr[7:5]);
    wire d_dirty0 = (d_line[37]==1'b1);
    wire d_dirty1 = (d_line[38]==1'b1);
    wire [15:0] d_w0 = d_line[17:2];
    wire [15:0] d_w1 = d_line[33:18];
    wire [15:0] d_cword = (d_wsel==1'b0) ? d_w0 : d_w1;

    wire d_miss = (is_ld | is_st) & ~d_hit;
    wire ld_fwd = is_ld & dfill_on & ~dfill_got & dfill_data_valid & (req_addr == dfill_miss);
    assign dmem_stall = (d_miss | dfill_busy) & ~ld_fwd;
    assign ld_data = d_hit ? d_cword : dfill_data;

    wire [7:0] d_sib = (dfill_miss[0]==1'b0) ? (dfill_miss + 8'd1) : (dfill_miss - 8'd1);
    assign dfill_addr = (~dfill_on & ~dfill_got) ? req_addr
                      : (~dfill_got ? dfill_miss : d_sib);
    assign dfill_busy = dfill_on | dfill_got;

    wire d_evict = d_miss & ~dfill_busy & d_full & (d_dirty0 | d_dirty1);
    assign dfill_req = dfill_on | dfill_got | (d_miss & ~dfill_busy & ~d_evict);

    wire fl_wb_en = is_flush & d_hit & ((d_wsel==1'b0) ? d_dirty0 : d_dirty1);
    assign wb_en      = d_evict;
    assign wb_word_en = d_evict | fl_wb_en;
    assign wb_wsel    = is_flush ? d_wsel : (d_dirty0 ? 1'b0 : 1'b1);
    assign wb_word_addr = {d_line[36:34], d_index, wb_wsel};
    assign wb_word_data = (wb_wsel==1'b0) ? d_w0 : d_w1;

    always @(posedge \posedge ) begin
        if (dfill_on & dfill_data_valid) begin
            if (~dfill_got) begin
                if (dfill_miss[0]==1'b0)
                    dcache[dfill_miss[4:1]] <= {3'b000, dfill_miss[7:5], 16'd0, dfill_data, 2'b00};
                else
                    dcache[dfill_miss[4:1]] <= {3'b000, dfill_miss[7:5], dfill_data, 16'd0, 2'b00};
                dfill_on <= 1'b0; dfill_got <= 1'b1;
            end else begin
                if (d_sib[0]==1'b0)
                    dcache[d_sib[4:1]] <= {3'b100, d_sib[7:5], dcache[d_sib[4:1]][33:18], dfill_data, 2'b00};
                else
                    dcache[d_sib[4:1]] <= {3'b100, d_sib[7:5], dfill_data, dcache[d_sib[4:1]][17:2], 2'b00};
                dfill_on <= 1'b0; dfill_got <= 1'b0;
            end
        end else if (~dfill_on & dfill_got) begin
            dfill_on <= 1'b1;
        end else if (~dfill_busy & d_miss & ~d_evict) begin
            dfill_on <= 1'b1; dfill_got <= 1'b0; dfill_miss <= req_addr;
        end
        if (is_st & d_hit & ~dmem_stall) begin
            if (d_wsel==1'b0)
                dcache[d_index] <= {1'b1, d_line[38], 1'b1, d_line[36:34], d_w1, st_data, 2'b00};
            else
                dcache[d_index] <= {1'b1, 1'b1, d_line[37], d_line[36:34], st_data, d_w0, 2'b00};
        end
        if (wb_word_en) begin
            if (wb_wsel==1'b0)
                dcache[d_index] <= {1'b1, d_line[38], 1'b0, d_line[36:34], d_w1, d_w0, 2'b00};
            else
                dcache[d_index] <= {1'b1, 1'b0, d_line[37], d_line[36:34], d_w1, d_w0, 2'b00};
        end
        if (rst) begin dfill_on <= 1'b0; dfill_got <= 1'b0; dfill_miss <= 8'd0; end   // synchronous reset (all scalars)
    end
endmodule
