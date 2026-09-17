// Hand-written "golden" SystemVerilog model of ooo_cpu_beqz_ref.ivy, the frozen stage-2
// snapshot of the out-of-order core (ALU ops and the conditional branch BEQZ: Tomasulo with
// a 4-entry re-order buffer, single dispatch, one ALU, a bimodal branch
// predictor, and misprediction recovery at retire), for combinational
// equivalence checking against the Ivy-generated RTL (ooo_cpu_beqz_ref.il) with
// rtlil_eqv (see check_ooo_golden.sh). It extends ooo_alu_golden.sv (stage 1).
//
// The register boundary matches the Ivy model exactly, register for register:
//
//   scalars   : pc, d_ir, d_valid, d_pred, d_pc, rob_head, rob_tail, ex_valid,
//               ex_idx, ex_ir, ex_a, ex_b -- synchronously reset by `rst`
//               (ivy_to_rtl emits every scalar register with a D = rst ? init :
//               next mux, the init value being that of `after init`, or 0).
//   banks     : rob_a_K, rob_a_rdy_K, rob_b_K, rob_b_rdy_K (K = 0..3) -- the
//               reservation-station operand fields, updated by the result
//               BROADCAST; rob_busy_K (K = 0..3) and rat_valid_R (R = 0..7) --
//               cleared wholesale by the SQUASH. Neither is a memory write
//               port, so ivy_to_rtl lowers these arrays to one register per
//               index with these names; they reset to their init (0) under rst.
//   memories  : mem, rf, rat_idx, rob_ir, rob_pc, rob_pred, rob_take,
//               rob_issued, rob_done, rob_val, rob_a_src, rob_b_src, and the
//               predictor's bp.bht -- point-written arrays, emitted as RTLIL
//               memories with a power-on $meminit (NOT reset by rst); modelled
//               here as Verilog memories with `initial` blocks. rtlil_eqv maps
//               both sides' memories to registers and pairs the words by name.
//
// The always-block below is a line-by-line transcription of the Ivy clock
// action, which is ordered (complete, retire [+ squash], issue, dispatch,
// fetch) with wire-based reads so that every value it reads is a pre-state
// value; it therefore has nonblocking semantics and transcribes directly.
// Ivy's sequential "later write wins" for two writes to one array in a cycle
// is the same as the later nonblocking assignment winning here.
//
// Instruction encoding: [15:13] opcode [12:10] rd [9:7] ra [6:4] rb [7:0] imm.
// Opcodes: 0 NOP, 1 ADD, 2 SUB, 3 LI (rd := zero_extend(imm8)),
//          6 BEQZ ra, imm8 (if rf[ra] == 0 then pc := imm8); 4,5,7 = NOP.

module cpu ( \posedge , rst );
    input \posedge ;
    input rst;

    // ---- architectural state ----
    reg [7:0]  pc;
    reg [15:0] rf  [0:7];
    reg [15:0] mem [0:255];         // instruction memory (program injected for sim; never written)

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

    // ---- ROB occupancy ----
    wire rob_full = sel_busy(rob_tail);
    wire retire   = sel_busy(rob_head) & rob_done[rob_head];

    // ---- dispatch decode ----
    wire [2:0] d_opcode = d_ir[15:13];
    wire [2:0] d_rd     = d_ir[12:10];
    wire [2:0] d_ra     = d_ir[9:7];
    wire [2:0] d_rb     = d_ir[6:4];
    wire [7:0] d_target = d_ir[7:0];
    wire d_alu     = (d_opcode == 3'd1) | (d_opcode == 3'd2) | (d_opcode == 3'd3);   // writes rd
    wire d_branch  = (d_opcode == 3'd6);
    wire d_exec    = d_alu | d_branch;                                                // goes through the ALU
    wire d_needs_a = (d_opcode == 3'd1) | (d_opcode == 3'd2) | (d_opcode == 3'd6);
    wire d_needs_b = (d_opcode == 3'd1) | (d_opcode == 3'd2);

    // ---- retire decode ----
    wire [15:0] r_ir     = rob_ir[rob_head];
    wire [2:0]  r_opcode = r_ir[15:13];
    wire [2:0]  r_rd     = r_ir[12:10];
    wire [7:0]  r_target = r_ir[7:0];
    wire        r_alu    = (r_opcode == 3'd1) | (r_opcode == 3'd2) | (r_opcode == 3'd3);
    wire        r_branch = (r_opcode == 3'd6);
    wire [15:0] r_val    = rob_val[rob_head];
    wire        r_rat_clear = sel_rat_valid(r_rd) & (rat_idx[r_rd] == rob_head);
    wire [7:0]  r_pc     = rob_pc[rob_head];
    wire        r_take   = rob_take[rob_head];
    wire        r_pred   = rob_pred[rob_head];
    // a retiring BEQZ whose outcome differs from its prediction: squash
    wire        squash   = retire & r_branch & (r_take != r_pred);
    wire [7:0]  redirect_pc = r_take ? r_target : (r_pc + 8'd1);

    wire dispatch = d_valid & ~rob_full & ~squash;
    wire if_stall = d_valid & rob_full;
    wire fetch_en = ~if_stall & ~squash;

    // ---- head-relative entry indices ----
    wire [1:0] h0 = rob_head;
    wire [1:0] h1 = rob_head + 2'd1;
    wire [1:0] h2 = rob_head + 2'd2;
    wire [1:0] h3 = rob_head + 2'd3;

    // ---- ALU ----
    wire [2:0] ex_opcode = ex_ir[15:13];
    wire [7:0] ex_target = ex_ir[7:0];
    wire [15:0] ex_res = (ex_opcode == 3'd1) ? (ex_a + ex_b) :
                         (ex_opcode == 3'd2) ? (ex_a - ex_b) :
                         (ex_opcode == 3'd3) ? {8'd0, ex_target} : 16'd0;
    wire ex_take = (ex_opcode == 3'd6) & (ex_a == 16'd0);       // the true BEQZ outcome

    // ---- operand capture at dispatch ----
    wire [1:0]  d_a_idx = rat_idx[d_ra];
    wire        d_a_bus = ex_valid & (ex_idx == d_a_idx);
    wire        d_a_rdy = ~d_needs_a | ~sel_rat_valid(d_ra) | rob_done[d_a_idx] | d_a_bus;
    wire [15:0] d_a_val = ~sel_rat_valid(d_ra) ? rf[d_ra] : (d_a_bus ? ex_res : rob_val[d_a_idx]);

    wire [1:0]  d_b_idx = rat_idx[d_rb];
    wire        d_b_bus = ex_valid & (ex_idx == d_b_idx);
    wire        d_b_rdy = ~d_needs_b | ~sel_rat_valid(d_rb) | rob_done[d_b_idx] | d_b_bus;
    wire [15:0] d_b_val = ~sel_rat_valid(d_rb) ? rf[d_rb] : (d_b_bus ? ex_res : rob_val[d_b_idx]);

    // ---- issue selection: oldest ready, un-issued entry (not during a squash) ----
    wire rdy0 = sel_busy(h0) & ~rob_issued[h0] & sel_a_rdy(h0) & sel_b_rdy(h0);
    wire rdy1 = sel_busy(h1) & ~rob_issued[h1] & sel_a_rdy(h1) & sel_b_rdy(h1);
    wire rdy2 = sel_busy(h2) & ~rob_issued[h2] & sel_a_rdy(h2) & sel_b_rdy(h2);
    wire rdy3 = sel_busy(h3) & ~rob_issued[h3] & sel_a_rdy(h3) & sel_b_rdy(h3);
    wire issue = ~squash & (rdy0 | rdy1 | rdy2 | rdy3);
    wire [1:0] issue_idx = rdy0 ? h0 : rdy1 ? h1 : rdy2 ? h2 : h3;

    // ---- operands of the issuing entry (bank reads; as wires so that the
    //      function calls do not synthesize into stray registers) ----
    wire [15:0] issue_a = sel_a(issue_idx);
    wire [15:0] issue_b = sel_b(issue_idx);

    // ---- the branch predictor: predict at fetch, train at retire ----
    wire bp_predicted_taken;
    bp bp (
        .\posedge (\posedge ), .rst(rst),
        .fetch_pc(pc), .br_valid(retire & r_branch), .br_pc(r_pc), .br_taken(r_take),
        .predicted_taken(bp_predicted_taken)
    );

    // ---- fetch and prediction ----
    wire [15:0] fetched = mem[pc];
    wire        f_is_branch = (fetched[15:13] == 3'd6);
    wire        f_ptaken    = f_is_branch & bp_predicted_taken;
    wire [7:0]  f_target    = fetched[7:0];
    wire [7:0]  pred_next_pc = f_ptaken ? f_target : (pc + 8'd1);

    // ---- result broadcast hits, per bank element ----
    wire hit_a0 = rob_busy_0 & (rob_a_src[0] == ex_idx);
    wire hit_a1 = rob_busy_1 & (rob_a_src[1] == ex_idx);
    wire hit_a2 = rob_busy_2 & (rob_a_src[2] == ex_idx);
    wire hit_a3 = rob_busy_3 & (rob_a_src[3] == ex_idx);
    wire hit_b0 = rob_busy_0 & (rob_b_src[0] == ex_idx);
    wire hit_b1 = rob_busy_1 & (rob_b_src[1] == ex_idx);
    wire hit_b2 = rob_busy_2 & (rob_b_src[2] == ex_idx);
    wire hit_b3 = rob_busy_3 & (rob_b_src[3] == ex_idx);

    always @(posedge \posedge ) begin
        // ---- complete: write the ALU result (and branch outcome) and broadcast ----
        if (ex_valid) begin
            rob_val[ex_idx]  <= ex_res;
            rob_done[ex_idx] <= 1'b1;
            rob_take[ex_idx] <= ex_take;
            if (hit_a0 & ~rob_a_rdy_0) rob_a_0 <= ex_res;   if (hit_a0) rob_a_rdy_0 <= 1'b1;
            if (hit_a1 & ~rob_a_rdy_1) rob_a_1 <= ex_res;   if (hit_a1) rob_a_rdy_1 <= 1'b1;
            if (hit_a2 & ~rob_a_rdy_2) rob_a_2 <= ex_res;   if (hit_a2) rob_a_rdy_2 <= 1'b1;
            if (hit_a3 & ~rob_a_rdy_3) rob_a_3 <= ex_res;   if (hit_a3) rob_a_rdy_3 <= 1'b1;
            if (hit_b0 & ~rob_b_rdy_0) rob_b_0 <= ex_res;   if (hit_b0) rob_b_rdy_0 <= 1'b1;
            if (hit_b1 & ~rob_b_rdy_1) rob_b_1 <= ex_res;   if (hit_b1) rob_b_rdy_1 <= 1'b1;
            if (hit_b2 & ~rob_b_rdy_2) rob_b_2 <= ex_res;   if (hit_b2) rob_b_rdy_2 <= 1'b1;
            if (hit_b3 & ~rob_b_rdy_3) rob_b_3 <= ex_res;   if (hit_b3) rob_b_rdy_3 <= 1'b1;
        end

        // ---- retire the head entry; a mispredicted BEQZ squashes everything behind it ----
        if (retire) begin
            if (r_alu) rf[r_rd] <= r_val;
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

        // ---- dispatch: allocate the tail entry, rename, capture operands ----
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
            rob_issued[rob_tail] <= ~d_exec;
            rob_done[rob_tail]   <= ~d_exec;
            rob_val[rob_tail]    <= 16'd0;
            rob_a_src[rob_tail]  <= d_a_idx;
            rob_b_src[rob_tail]  <= d_b_idx;
            if (d_alu) begin
                case (d_rd)
                    3'd0: rat_valid_0 <= 1'b1; 3'd1: rat_valid_1 <= 1'b1;
                    3'd2: rat_valid_2 <= 1'b1; 3'd3: rat_valid_3 <= 1'b1;
                    3'd4: rat_valid_4 <= 1'b1; 3'd5: rat_valid_5 <= 1'b1;
                    3'd6: rat_valid_6 <= 1'b1; default: rat_valid_7 <= 1'b1;
                endcase
                rat_idx[d_rd] <= rob_tail;
            end
            rob_tail <= rob_tail + 2'd1;
        end

        // ---- fetch along the predicted path, unless stalled or squashing ----
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
