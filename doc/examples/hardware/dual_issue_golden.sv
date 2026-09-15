// Hand-written "golden" SystemVerilog model of the dual_issue_cpu_ref datapath,
// for combinational equivalence checking against the Ivy-generated RTL
// (dual_issue_cpu_ref.il). Register and memory names match the Ivy model exactly
// (after flatten) so yosys equiv_make can pair them up.
//
// This is the 2-wide (dual-issue, in-order superscalar) 5-stage CPU whose memory
// subsystem is the reusable `idcache` module, instantiated as `idc`. The idcache
// internals (main_mem + ic + dc) and the branch predictor `bp` are identical to
// the single-issue gen CPU (cpu_gen_golden.sv); the only idcache change here is
// that `ic`/`idcache` also export the lane-1 fetch outputs (fetch_data1/
// fetch_valid1: the odd sibling word of the fetched line). The proof-only
// interface isolates (mem_ic/mem_dc and their props) hold no RTL state and are
// omitted. rst is tied to 0 for the check.
//
// Bit layouts (same as the gen CPU):
//   icline (36): [35] full | [34:32] tag | [31:16] word1 | [15:0] word0
//   dcline (40): [39] full | [38] d1 | [37] d0 | [36:34] tag | [33:18] w1
//                | [17:2] w0 | [1:0] (unused 0)
//   addr (8):    [7:5] tag | [4:1] index | [0] wsel

// ===========================================================================
// CPU top: dual-issue pipeline datapath + register file, instantiating bp/idc.
// Lane 1 = the `1`-suffixed registers/wires. Only lane 0 may hold a branch or
// FLUSH; lane 1 issues (issue_two) as the aligned odd-sibling fall-through.
// ===========================================================================
module cpu ( \posedge , rst );
    input \posedge ;
    input rst;

    reg [7:0]  pc;
    reg [15:0] rf [0:7];

    // lane 0 pipeline latches
    reg [15:0] d_ir;  reg d_valid; reg d_pred; reg [7:0] d_pc;
    reg [15:0] e_ir;  reg e_valid; reg e_pred; reg [7:0] e_pc;
    reg [15:0] m_ir;  reg m_valid; reg [15:0] m_res; reg [7:0] m_addr; reg [15:0] m_store;
    reg [15:0] w_ir;  reg w_valid; reg [15:0] w_val;
    // lane 1 pipeline latches
    reg [15:0] d_ir1; reg d_valid1; reg d_pred1; reg [7:0] d_pc1;
    reg [15:0] e_ir1; reg e_valid1; reg e_pred1; reg [7:0] e_pc1;
    reg [15:0] m_ir1; reg m_valid1; reg [15:0] m_res1; reg [7:0] m_addr1; reg [15:0] m_store1;
    reg [15:0] w_ir1; reg w_valid1; reg [15:0] w_val1;

    // ---- init (matches the Ivy `after init`; init-only, ignored by equiv_induct) ----
    integer ri;
    initial begin
        pc = 8'd0;
        d_valid = 1'b0; e_valid = 1'b0; m_valid = 1'b0; w_valid = 1'b0;
        d_valid1 = 1'b0; e_valid1 = 1'b0; m_valid1 = 1'b0; w_valid1 = 1'b0;
        for (ri = 0; ri < 8; ri = ri + 1) rf[ri] = 16'd0;
    end

    // ---- decode wires ----
    wire [2:0] d_opcode  = d_ir[15:13];
    wire [2:0] e_opcode  = e_ir[15:13];
    wire [2:0] e_rd      = e_ir[12:10];
    wire [2:0] e_ra      = e_ir[9:7];
    wire [2:0] e_rb      = e_ir[6:4];
    wire [7:0] e_target  = e_ir[7:0];
    wire [2:0] m_opcode  = m_ir[15:13];
    wire [2:0] m_rd      = m_ir[12:10];
    wire [2:0] w_opcode  = w_ir[15:13];
    wire [2:0] w_rd      = w_ir[12:10];
    wire [2:0] e_opcode1 = e_ir1[15:13];
    wire [2:0] e_rd1     = e_ir1[12:10];
    wire [2:0] e_ra1     = e_ir1[9:7];
    wire [2:0] e_rb1     = e_ir1[6:4];
    wire [7:0] e_target1 = e_ir1[7:0];
    wire [2:0] m_opcode1 = m_ir1[15:13];
    wire [2:0] m_rd1     = m_ir1[12:10];
    wire [2:0] w_opcode1 = w_ir1[15:13];
    wire [2:0] w_rd1     = w_ir1[12:10];

    // ---- EX operands (direct rf reads; RAW hazards resolved by stall) ----
    wire [15:0] e_a = rf[e_ra];
    wire [15:0] e_b = rf[e_rb];
    wire e_take = (e_opcode == 3'd6) & (e_a == 16'd0);

    wire e_lane0_wr = e_valid & (e_opcode==3'd1 | e_opcode==3'd2 | e_opcode==3'd3);
    wire [15:0] e_res =
        (e_opcode==3'd1) ? (e_a + e_b) :
        (e_opcode==3'd2) ? (e_a - e_b) :
        (e_opcode==3'd3) ? {8'd0, e_target} : 16'd0;

    // lane-1 operands with the ONLY forwarding path: intra-bundle lane0 -> lane1
    wire [15:0] e_a1 = rf[e_ra1];
    wire [15:0] e_b1 = rf[e_rb1];
    wire [15:0] e_a1_fwd = (e_lane0_wr & (e_rd == e_ra1)) ? e_res : e_a1;
    wire [15:0] e_b1_fwd = (e_lane0_wr & (e_rd == e_rb1)) ? e_res : e_b1;
    wire [15:0] e_res1 =
        (e_opcode1==3'd1) ? (e_a1_fwd + e_b1_fwd) :
        (e_opcode1==3'd2) ? (e_a1_fwd - e_b1_fwd) :
        (e_opcode1==3'd3) ? {8'd0, e_target1} : 16'd0;

    // ---- register-file writer slots (both lanes of MEM and WB) ----
    wire m0_wr = m_valid  & (m_opcode ==3'd1 | m_opcode ==3'd2 | m_opcode ==3'd3 | m_opcode ==3'd4);
    wire m1_wr = m_valid1 & (m_opcode1==3'd1 | m_opcode1==3'd2 | m_opcode1==3'd3 | m_opcode1==3'd4);
    wire w0_wr = w_valid  & (w_opcode ==3'd1 | w_opcode ==3'd2 | w_opcode ==3'd3 | w_opcode ==3'd4);
    wire w1_wr = w_valid1 & (w_opcode1==3'd1 | w_opcode1==3'd2 | w_opcode1==3'd3 | w_opcode1==3'd4);

    // which MEM lane holds the (single) memory op
    wire mem_l1 = m_valid1 & (m_opcode1==3'd4 | m_opcode1==3'd5);

    // ---- data-hazard stall: any EX source matches a MEM/WB writer's dest ----
    wire hz_ea  = (m0_wr & m_rd==e_ra)  | (m1_wr & m_rd1==e_ra)  | (w0_wr & w_rd==e_ra)  | (w1_wr & w_rd1==e_ra);
    wire hz_eb  = (m0_wr & m_rd==e_rb)  | (m1_wr & m_rd1==e_rb)  | (w0_wr & w_rd==e_rb)  | (w1_wr & w_rd1==e_rb);
    wire hz_ea1 = (m0_wr & m_rd==e_ra1) | (m1_wr & m_rd1==e_ra1) | (w0_wr & w_rd==e_ra1) | (w1_wr & w_rd1==e_ra1);
    wire hz_eb1 = (m0_wr & m_rd==e_rb1) | (m1_wr & m_rd1==e_rb1) | (w0_wr & w_rd==e_rb1) | (w1_wr & w_rd1==e_rb1);
    wire ex_stall = (e_valid  & (hz_ea  | hz_eb))
                  | (e_valid1 & (hz_ea1 | hz_eb1));

    wire mispredict = e_valid & ~ex_stall & (e_opcode==3'd6) & (e_pred != e_take);

    // ---- branch predictor ----
    wire br_valid = e_valid & (e_opcode==3'd6) & ~ex_stall;
    wire predicted_taken;
    bp bp (
        .\posedge (\posedge ), .rst(rst),
        .fetch_pc(pc), .br_valid(br_valid), .br_pc(e_pc), .br_taken(e_take),
        .predicted_taken(predicted_taken)
    );

    // ---- fetch stall on a pending FLUSH (lane 0 only; FLUSH never issues to lane 1) ----
    wire flush_in_pipe = (d_valid & d_opcode==3'd7)
                       | (e_valid & e_opcode==3'd7)
                       | (m_valid & m_opcode==3'd7);

    // ---- the idcache module ----
    wire fetch_active = ~ex_stall & ~mispredict & ~flush_in_pipe;
    wire [15:0] idc_fetch_data0, idc_fetch_data1, idc_read_data;
    wire        idc_fetch_valid0, idc_fetch_valid1, idc_data_stall;
    idcache idc (
        .\posedge (\posedge ), .rst(rst),
        .fetch_req (fetch_active),
        .fetch_addr(pc),
        .read_req  ((m_valid & (m_opcode==3'd4)) | (m_valid1 & (m_opcode1==3'd4))),
        .write_req ((m_valid & (m_opcode==3'd5)) | (m_valid1 & (m_opcode1==3'd5))),
        .flush_req ((m_valid & (m_opcode==3'd7)) | (m_valid1 & (m_opcode1==3'd7))),
        .data_addr (mem_l1 ? m_addr1  : m_addr),
        .write_data(mem_l1 ? m_store1 : m_store),
        .fetch_data0 (idc_fetch_data0),  .fetch_valid0(idc_fetch_valid0),
        .fetch_data1 (idc_fetch_data1),  .fetch_valid1(idc_fetch_valid1),
        .read_data   (idc_read_data),    .data_stall  (idc_data_stall)
    );

    wire [15:0] fetched      = idc_fetch_data0;
    wire [15:0] fetched1     = idc_fetch_data1;
    wire        ifetch_stall = ~idc_fetch_valid0;
    wire        dmem_stall   = idc_data_stall;

    wire f_is_branch = (fetched[15:13]==3'd6);
    wire f_ptaken    = f_is_branch & predicted_taken;
    wire [7:0] f_target = fetched[7:0];
    wire [7:0] pred_next_pc = f_ptaken ? f_target : (pc + 8'd1);

    // ---- issue-two (dual-issue) decision ----
    wire [2:0] f_op0 = fetched[15:13];
    wire [2:0] f_op1 = fetched1[15:13];
    wire [2:0] f_rd0 = fetched[12:10];
    wire [2:0] f_ra1 = fetched1[9:7];
    wire [2:0] f_rb1 = fetched1[6:4];
    wire f_nonbranch1 = (f_op1 != 3'd6);
    wire f_mem0 = (f_op0==3'd4 | f_op0==3'd5);
    wire f_mem1 = (f_op1==3'd4 | f_op1==3'd5);
    wire f_ld_use = (f_op0==3'd4) & (f_rd0==f_ra1 | f_rd0==f_rb1);
    wire issue_two = ~dmem_stall & ~ex_stall & ~mispredict & ~flush_in_pipe
                   & ~ifetch_stall & idc_fetch_valid1
                   & ~f_ptaken & f_nonbranch1
                   & (f_op0 != 3'd7) & (f_op1 != 3'd7)
                   & ~(f_mem0 & f_mem1)
                   & ~f_ld_use;

    always @(posedge \posedge ) begin
        // WB: retire (lane 0 then lane 1 -> lane 1 wins a same-rd tie)
        if (w0_wr) rf[w_rd]  <= w_val;
        if (w1_wr) rf[w_rd1] <= w_val1;

        // MEM -> WB latch (unconditional; valids gated by ~dmem_stall)
        w_ir     <= m_ir;
        w_valid  <= m_valid & ~dmem_stall;
        w_val    <= (m_opcode  != 3'd4) ? m_res  : idc_read_data;
        w_ir1    <= m_ir1;
        w_valid1 <= m_valid1 & ~dmem_stall;
        w_val1   <= (m_opcode1 != 3'd4) ? m_res1 : idc_read_data;

        // EX -> MEM
        if (dmem_stall) begin
        end else if (ex_stall) begin
            m_valid  <= 1'b0;
            m_valid1 <= 1'b0;
        end else begin
            m_ir     <= e_ir;
            m_valid  <= e_valid;
            m_res    <= e_res;
            m_addr   <= e_a[7:0];
            m_store  <= e_b;
            m_ir1    <= e_ir1;
            m_valid1 <= e_valid1 & ~mispredict;
            m_res1   <= e_res1;
            m_addr1  <= e_a1_fwd[7:0];
            m_store1 <= e_b1_fwd;
        end

        // ID -> EX and IF -> ID
        if (~dmem_stall & ~ex_stall) begin
            if (mispredict) begin
                e_valid  <= 1'b0;
                d_valid  <= 1'b0;
                e_valid1 <= 1'b0;
                d_valid1 <= 1'b0;
                pc       <= e_take ? e_target : (e_pc + 8'd1);
            end else begin
                e_ir    <= d_ir;
                e_valid <= d_valid;
                e_pred  <= d_pred;
                e_pc    <= d_pc;
                e_ir1   <= d_ir1;
                e_valid1<= d_valid1;
                e_pred1 <= d_pred1;
                e_pc1   <= d_pc1;
                if (flush_in_pipe | ifetch_stall) begin
                    d_valid  <= 1'b0;
                    d_valid1 <= 1'b0;
                end else begin
                    d_ir    <= fetched;
                    d_valid <= 1'b1;
                    d_pred  <= f_ptaken;
                    d_pc    <= pc;
                    d_ir1   <= fetched1;
                    d_valid1<= issue_two;
                    d_pred1 <= 1'b0;
                    d_pc1   <= pc + 8'd1;
                    pc      <= issue_two ? (pc + 8'd2) : pred_next_pc;
                end
            end
        end
    end
endmodule

// ===========================================================================
// idcache: wires up main_mem + ic + dc; now also routes lane-1 fetch outputs.
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
    end
endmodule

// ===========================================================================
// Branch predictor: bimodal 2-bit saturating counters (mirrors cpu.bp).
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
