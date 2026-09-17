// Hand-written "golden" SystemVerilog model of ooo_cpu_ref.ivy (stage 1: the
// ALU-only out-of-order core -- Tomasulo with a 4-entry re-order buffer, single
// dispatch, one ALU), for combinational equivalence checking against the
// Ivy-generated RTL (ooo_cpu_ref.il) with rtlil_eqv (see check_ooo_golden.sh).
//
// The register boundary matches the Ivy model exactly, register for register:
//
//   scalars   : pc, d_ir, d_valid, rob_head, rob_tail, ex_valid, ex_idx, ex_ir,
//               ex_a, ex_b           -- synchronously reset by `rst` (ivy_to_rtl
//               emits every scalar register with a D = rst ? init : next mux,
//               the init value being that of `after init`, or 0 if none).
//   banks     : rob_a_K, rob_a_rdy_K, rob_b_K, rob_b_rdy_K (K = 0..3) -- the
//               reservation-station operand fields. In Ivy these are arrays
//               updated by the result BROADCAST (every entry waiting on the
//               completing tag captures it in one cycle), which is not a memory
//               write port, so ivy_to_rtl lowers them to one register per index
//               with these names; they reset to 0 under `rst`.
//   memories  : mem, rf, rat_valid, rat_idx, rob_busy, rob_ir, rob_issued,
//               rob_done, rob_val, rob_a_src, rob_b_src -- point-written arrays,
//               emitted as RTLIL memories with a power-on $meminit (NOT reset by
//               `rst`); modelled here as Verilog memories with `initial` blocks.
//               rtlil_eqv maps both sides' memories to registers (memory_map)
//               and pairs the words by name (rf[0], ...); initial values are
//               ignored (registers are cut points).
//
// The always-block below is a line-by-line transcription of the Ivy clock
// action. The Ivy action was ordered (complete, retire, issue, dispatch, fetch)
// and given wire-based reads so that every value it reads is a pre-state value;
// it therefore has nonblocking semantics and transcribes directly. Ivy's
// sequential "later write wins" for two writes to one array in a cycle is the
// same as the later nonblocking assignment winning here.
//
// Instruction encoding: [15:13] opcode [12:10] rd [9:7] ra [6:4] rb [7:0] imm.
// Opcodes: 0 NOP, 1 ADD, 2 SUB, 3 LI (rd := zero_extend(imm8)); 4..7 = NOP.

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

    // ---- rename table ----
    reg        rat_valid [0:7];
    reg [1:0]  rat_idx   [0:7];

    // ---- re-order buffer ----
    reg [1:0]  rob_head;
    reg [1:0]  rob_tail;
    reg        rob_busy   [0:3];
    reg [15:0] rob_ir     [0:3];
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
        for (ii = 0; ii < 8; ii = ii + 1) begin rf[ii] = 16'd0; rat_valid[ii] = 1'b0; end
        for (ii = 0; ii < 4; ii = ii + 1) begin rob_busy[ii] = 1'b0; rob_issued[ii] = 1'b0; rob_done[ii] = 1'b0; end
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

    // ---- ROB occupancy ----
    wire rob_full = rob_busy[rob_tail];
    wire retire   = rob_busy[rob_head] & rob_done[rob_head];

    // ---- dispatch decode ----
    wire [2:0] d_opcode = d_ir[15:13];
    wire [2:0] d_rd     = d_ir[12:10];
    wire [2:0] d_ra     = d_ir[9:7];
    wire [2:0] d_rb     = d_ir[6:4];
    wire [7:0] d_target = d_ir[7:0];
    wire d_alu      = (d_opcode == 3'd1) | (d_opcode == 3'd2) | (d_opcode == 3'd3);
    wire d_needs_ab = (d_opcode == 3'd1) | (d_opcode == 3'd2);
    wire dispatch   = d_valid & ~rob_full;
    wire if_stall   = d_valid & rob_full;

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

    // ---- operand capture at dispatch ----
    wire [1:0]  d_a_idx = rat_idx[d_ra];
    wire        d_a_bus = ex_valid & (ex_idx == d_a_idx);
    wire        d_a_rdy = ~d_needs_ab | ~rat_valid[d_ra] | rob_done[d_a_idx] | d_a_bus;
    wire [15:0] d_a_val = ~rat_valid[d_ra] ? rf[d_ra] : (d_a_bus ? ex_res : rob_val[d_a_idx]);

    wire [1:0]  d_b_idx = rat_idx[d_rb];
    wire        d_b_bus = ex_valid & (ex_idx == d_b_idx);
    wire        d_b_rdy = ~d_needs_ab | ~rat_valid[d_rb] | rob_done[d_b_idx] | d_b_bus;
    wire [15:0] d_b_val = ~rat_valid[d_rb] ? rf[d_rb] : (d_b_bus ? ex_res : rob_val[d_b_idx]);

    // ---- issue selection: oldest ready, un-issued entry ----
    wire rdy0 = rob_busy[h0] & ~rob_issued[h0] & sel_a_rdy(h0) & sel_b_rdy(h0);
    wire rdy1 = rob_busy[h1] & ~rob_issued[h1] & sel_a_rdy(h1) & sel_b_rdy(h1);
    wire rdy2 = rob_busy[h2] & ~rob_issued[h2] & sel_a_rdy(h2) & sel_b_rdy(h2);
    wire rdy3 = rob_busy[h3] & ~rob_issued[h3] & sel_a_rdy(h3) & sel_b_rdy(h3);
    wire issue = rdy0 | rdy1 | rdy2 | rdy3;
    wire [1:0] issue_idx = rdy0 ? h0 : rdy1 ? h1 : rdy2 ? h2 : h3;

    // ---- operands of the issuing entry (bank reads; as wires so that the
    //      function calls do not synthesize into stray registers) ----
    wire [15:0] issue_a = sel_a(issue_idx);
    wire [15:0] issue_b = sel_b(issue_idx);

    // ---- retire decode ----
    wire [15:0] r_ir     = rob_ir[rob_head];
    wire [2:0]  r_opcode = r_ir[15:13];
    wire [2:0]  r_rd     = r_ir[12:10];
    wire        r_alu    = (r_opcode == 3'd1) | (r_opcode == 3'd2) | (r_opcode == 3'd3);
    wire [15:0] r_val    = rob_val[rob_head];
    wire        r_rat_clear = rat_valid[r_rd] & (rat_idx[r_rd] == rob_head);

    // ---- result broadcast hits, per bank element ----
    wire hit_a0 = rob_busy[0] & (rob_a_src[0] == ex_idx);
    wire hit_a1 = rob_busy[1] & (rob_a_src[1] == ex_idx);
    wire hit_a2 = rob_busy[2] & (rob_a_src[2] == ex_idx);
    wire hit_a3 = rob_busy[3] & (rob_a_src[3] == ex_idx);
    wire hit_b0 = rob_busy[0] & (rob_b_src[0] == ex_idx);
    wire hit_b1 = rob_busy[1] & (rob_b_src[1] == ex_idx);
    wire hit_b2 = rob_busy[2] & (rob_b_src[2] == ex_idx);
    wire hit_b3 = rob_busy[3] & (rob_b_src[3] == ex_idx);

    always @(posedge \posedge ) begin
        // ---- complete: write the ALU result and broadcast it ----
        if (ex_valid) begin
            rob_val[ex_idx]  <= ex_res;
            rob_done[ex_idx] <= 1'b1;
            if (hit_a0 & ~rob_a_rdy_0) rob_a_0 <= ex_res;   if (hit_a0) rob_a_rdy_0 <= 1'b1;
            if (hit_a1 & ~rob_a_rdy_1) rob_a_1 <= ex_res;   if (hit_a1) rob_a_rdy_1 <= 1'b1;
            if (hit_a2 & ~rob_a_rdy_2) rob_a_2 <= ex_res;   if (hit_a2) rob_a_rdy_2 <= 1'b1;
            if (hit_a3 & ~rob_a_rdy_3) rob_a_3 <= ex_res;   if (hit_a3) rob_a_rdy_3 <= 1'b1;
            if (hit_b0 & ~rob_b_rdy_0) rob_b_0 <= ex_res;   if (hit_b0) rob_b_rdy_0 <= 1'b1;
            if (hit_b1 & ~rob_b_rdy_1) rob_b_1 <= ex_res;   if (hit_b1) rob_b_rdy_1 <= 1'b1;
            if (hit_b2 & ~rob_b_rdy_2) rob_b_2 <= ex_res;   if (hit_b2) rob_b_rdy_2 <= 1'b1;
            if (hit_b3 & ~rob_b_rdy_3) rob_b_3 <= ex_res;   if (hit_b3) rob_b_rdy_3 <= 1'b1;
        end

        // ---- retire the head entry ----
        if (retire) begin
            if (r_alu)       rf[r_rd]        <= r_val;
            if (r_rat_clear) rat_valid[r_rd] <= 1'b0;
            rob_busy[rob_head] <= 1'b0;
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
            rob_busy[rob_tail]   <= 1'b1;
            rob_ir[rob_tail]     <= d_ir;
            rob_issued[rob_tail] <= ~d_alu;
            rob_done[rob_tail]   <= ~d_alu;
            rob_val[rob_tail]    <= 16'd0;
            case (rob_tail)
                2'd0: begin rob_a_0 <= d_a_val; rob_a_rdy_0 <= d_a_rdy; rob_b_0 <= d_b_val; rob_b_rdy_0 <= d_b_rdy; end
                2'd1: begin rob_a_1 <= d_a_val; rob_a_rdy_1 <= d_a_rdy; rob_b_1 <= d_b_val; rob_b_rdy_1 <= d_b_rdy; end
                2'd2: begin rob_a_2 <= d_a_val; rob_a_rdy_2 <= d_a_rdy; rob_b_2 <= d_b_val; rob_b_rdy_2 <= d_b_rdy; end
                default: begin rob_a_3 <= d_a_val; rob_a_rdy_3 <= d_a_rdy; rob_b_3 <= d_b_val; rob_b_rdy_3 <= d_b_rdy; end
            endcase
            rob_a_src[rob_tail]  <= d_a_idx;
            rob_b_src[rob_tail]  <= d_b_idx;
            if (d_alu) begin
                rat_valid[d_rd] <= 1'b1;
                rat_idx[d_rd]   <= rob_tail;
            end
            rob_tail <= rob_tail + 2'd1;
        end

        // ---- fetch, unless dispatch is stalled on a full ROB ----
        if (~if_stall) begin
            d_ir    <= mem[pc];
            d_valid <= 1'b1;
            pc      <= pc + 8'd1;
        end

        // ---- synchronous reset of every scalar/bank register (the Ivy
        //      `after init` values; registers it does not mention reset to 0,
        //      as ivy_to_rtl emits them). Memories are not reset. ----
        if (rst) begin
            pc <= 8'd0; d_ir <= 16'd0; d_valid <= 1'b0;
            rob_head <= 2'd0; rob_tail <= 2'd0;
            ex_valid <= 1'b0; ex_idx <= 2'd0; ex_ir <= 16'd0; ex_a <= 16'd0; ex_b <= 16'd0;
            rob_a_0 <= 16'd0; rob_a_1 <= 16'd0; rob_a_2 <= 16'd0; rob_a_3 <= 16'd0;
            rob_b_0 <= 16'd0; rob_b_1 <= 16'd0; rob_b_2 <= 16'd0; rob_b_3 <= 16'd0;
            rob_a_rdy_0 <= 1'b0; rob_a_rdy_1 <= 1'b0; rob_a_rdy_2 <= 1'b0; rob_a_rdy_3 <= 1'b0;
            rob_b_rdy_0 <= 1'b0; rob_b_rdy_1 <= 1'b0; rob_b_rdy_2 <= 1'b0; rob_b_rdy_3 <= 1'b0;
        end
    end
endmodule
