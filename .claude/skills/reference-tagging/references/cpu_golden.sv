// Hand-written "golden" SystemVerilog model of the 5stage_cache_cpu_ref
// datapath, for combinational equivalence checking against the Ivy-generated
// RTL (5stage_cache_cpu_ref.il). Register and memory names match the Ivy model
// exactly so yosys equiv_make can pair them up. This is an independent
// transcription of the datapath in `object cpu` (the `after posedge` action and
// its combinational wire definitions); the proof-only trace/ghost state is not
// part of the hardware and is absent here.
//
// Line format (cline, 22 bits): [21] full | [20] dirty | [19:16] hi_addr | [15:0] data
// bfe[i][j](x) is x[j:i]; concat(a,b,..) is {a,b,..} (first arg = MSBs).
//
// The clock is the Ivy "posedge" net; `rst` is Ivy's synchronous reset (a mux
// select on every register's D input). Equivalence is checked with rst tied to
// 0 (normal operation), so the reset init values are not modelled here.
//
// The branch predictor is the sub-module `bp` (mirroring the Ivy sub-isolate
// cpu.bp), instantiated as `bp`. cpu_equiv.ys flattens both designs, so the
// predictor's bht memory pairs up by the flattened name bp.bht.

module cpu (
    \posedge ,          // clock (Ivy's exported `posedge` action)
    rst                 // synchronous reset (unused here; tied to 0 for the check)
);
    input \posedge ;
    input rst;

    // ---- architectural state / pipeline latches (names match the Ivy model) --
    reg [7:0]  pc;
    reg [15:0] rf   [0:7];      // 8 x word
    reg [15:0] mem  [0:255];    // 256 x word (unified memory)
    reg [21:0] dcache [0:15];   // 16 x cline
    reg [21:0] icache [0:15];   // 16 x cline

    reg [15:0] d_ir;  reg d_valid; reg d_pred; reg [7:0] d_pc;
    reg [15:0] e_ir;  reg e_valid; reg e_pred; reg [7:0] e_pc;
    reg [15:0] m_ir;  reg m_valid; reg [15:0] m_res; reg [7:0] m_addr; reg [15:0] m_store;
    reg [15:0] w_ir;  reg w_valid; reg [15:0] w_val;

    reg mbusy; reg [7:0] mfa; reg mfi;

    // ---- decode wires ----
    wire [2:0] d_opcode = d_ir[15:13];
    wire [2:0] e_opcode = e_ir[15:13];
    wire [2:0] e_rd     = e_ir[12:10];
    wire [2:0] e_ra     = e_ir[9:7];
    wire [2:0] e_rb     = e_ir[6:4];
    wire [7:0] e_target = e_ir[7:0];
    wire [2:0] m_opcode = m_ir[15:13];
    wire [2:0] m_rd     = m_ir[12:10];
    wire [2:0] w_opcode = w_ir[15:13];
    wire [2:0] w_rd     = w_ir[12:10];

    // ---- EX operands and the true branch decision ----
    wire [15:0] e_a = rf[e_ra];
    wire [15:0] e_b = rf[e_rb];
    wire e_take = (e_opcode == 3'd6) & (e_a == 16'd0);

    // ---- data-hazard stall ----
    wire ex_stall = e_valid & (
        (m_valid & (m_opcode==3'd1 | m_opcode==3'd2 | m_opcode==3'd3 | m_opcode==3'd4)
                 & (m_rd==e_ra | m_rd==e_rb)) |
        (w_valid & (w_opcode==3'd1 | w_opcode==3'd2 | w_opcode==3'd3 | w_opcode==3'd4)
                 & (w_rd==e_ra | w_rd==e_rb)));

    // ---- misprediction ----
    wire mispredict = e_valid & ~ex_stall & (e_opcode==3'd6) & (e_pred != e_take);

    // ---- branch predictor (sub-module, mirrors the Ivy sub-isolate cpu.bp) ----
    wire br_valid = e_valid & (e_opcode==3'd6) & ~ex_stall;
    wire predicted_taken;
    bp bp (
        .\posedge (\posedge ),
        .rst      (rst),
        .fetch_pc (pc),
        .br_valid (br_valid),
        .br_pc    (e_pc),
        .br_taken (e_take),
        .predicted_taken (predicted_taken)
    );

    // ---- fetch stall on a pending FLUSH ----
    wire flush_in_pipe = (d_valid & d_opcode==3'd7)
                       | (e_valid & e_opcode==3'd7)
                       | (m_valid & m_opcode==3'd7);

    // ---- fetch and prediction (through the I-cache) ----
    wire [3:0]  f_index = pc[3:0];
    wire [21:0] f_iline = icache[f_index];
    wire f_ihit = (f_iline[21]==1'b1) & (f_iline[19:16] == pc[7:4]);
    wire [15:0] fetched = f_ihit ? f_iline[15:0] : mem[pc];
    wire f_is_branch = (fetched[15:13]==3'd6);
    wire f_ptaken = f_is_branch & predicted_taken;
    wire [7:0] f_target = fetched[7:0];
    wire [7:0] pred_next_pc = f_ptaken ? f_target : (pc + 8'd1);

    // ---- instruction-fetch fill stall ----
    wire fetch_active = ~ex_stall & ~mispredict & ~flush_in_pipe;
    wire i_fill_go = mbusy & mfi & (mfa == pc);
    wire ifetch_stall = ~f_ihit & ~i_fill_go;

    // ---- MEM-stage D-cache access ----
    wire [3:0]  m_index = m_addr[3:0];
    wire [3:0]  m_hi    = m_addr[7:4];
    wire [21:0] m_line  = dcache[m_index];
    wire m_line_full  = (m_line[21]==1'b1);
    wire m_line_dirty = (m_line[20]==1'b1);
    wire [3:0]  m_line_hi   = m_line[19:16];
    wire [15:0] m_line_data = m_line[15:0];
    wire m_hit = m_line_full & (m_line_hi == m_hi);
    wire [21:0] m_iline = icache[m_index];
    wire m_ihit = (m_iline[21]==1'b1) & (m_iline[19:16] == m_hi);
    wire [7:0] m_victim_addr = {m_line_hi, m_index};
    wire [15:0] m_fill_data = mem[m_addr];

    // ---- D-cache read-fill stall ----
    wire d_miss = m_valid & (m_opcode==3'd4) & ~m_hit;
    wire d_fill_go = mbusy & ~mfi & (mfa == m_addr);
    wire dmem_stall = d_miss & ~d_fill_go;

    // ---- MEM ALU result and WB writeback value ----
    wire [15:0] m_res_next =
        (e_opcode==3'd1) ? (e_a + e_b) :
        (e_opcode==3'd2) ? (e_a - e_b) :
        (e_opcode==3'd3) ? {8'd0, e_target} : 16'd0;
    wire [15:0] w_val_next =
        (m_opcode != 3'd4) ? m_res : (m_hit ? m_line_data : m_fill_data);

    // integer index temporaries for the memory loops
    integer i;

    always @(posedge \posedge ) begin
        // ---- WB: retire (write the register file) ----
        if (w_valid & (w_opcode==3'd1 | w_opcode==3'd2 | w_opcode==3'd3 | w_opcode==3'd4))
            rf[w_rd] <= w_val;

        // ---- MEM -> WB latch ----
        w_ir    <= m_ir;
        w_valid <= m_valid & ~dmem_stall;
        w_val   <= w_val_next;

        // ---- D-cache update (LD/ST), unless MEM is stalled for a fill ----
        if (~dmem_stall & m_valid & (m_opcode==3'd4 | m_opcode==3'd5)) begin
            // write the dirty victim back on a miss
            if (~m_hit & m_line_full & m_line_dirty)
                mem[m_victim_addr] <= m_line_data;
            if (m_opcode==3'd5)
                dcache[m_index] <= {1'b1, 1'b1, m_hi, m_store};       // ST install (dirty)
            else if (~m_hit)
                dcache[m_index] <= {1'b1, 1'b0, m_hi, m_fill_data};   // LD-miss install (clean)
        end

        // ---- FLUSH: write back if dirty, then evict from both caches ----
        if (~dmem_stall & m_valid & (m_opcode==3'd7)) begin
            if (m_hit & m_line_dirty)
                mem[m_addr] <= m_line_data;
            if (m_hit)  dcache[m_index] <= 22'd0;
            if (m_ihit) icache[m_index] <= 22'd0;
        end

        // ---- EX -> MEM ----
        if (dmem_stall) begin
            // MEM held: m_* keep their values
        end else if (ex_stall) begin
            m_valid <= 1'b0;                 // bubble MEM
        end else begin
            m_ir    <= e_ir;
            m_valid <= e_valid;
            m_res   <= m_res_next;
            m_addr  <= e_a[7:0];             // bfe[0][7](e_a)
            m_store <= e_b;
        end

        // ---- ID -> EX and IF -> ID ----
        if (~dmem_stall & ~ex_stall) begin
            if (mispredict) begin
                e_valid <= 1'b0;                                  // squash ID instr
                d_valid <= 1'b0;                                  // squash fetch
                pc      <= e_take ? e_target : (e_pc + 8'd1);     // redirect
            end else begin
                // ID -> EX
                e_ir   <= d_ir;
                e_valid<= d_valid;
                e_pred <= d_pred;
                e_pc   <= d_pc;
                // IF -> ID
                if (flush_in_pipe | ifetch_stall) begin
                    d_valid <= 1'b0;                              // bubble; hold PC
                end else begin
                    d_ir   <= fetched;
                    d_valid<= 1'b1;
                    d_pred <= f_ptaken;
                    d_pc   <= pc;
                    if (~f_ihit)
                        icache[f_index] <= {1'b1, 1'b0, pc[7:4], fetched};  // I-fill install
                    pc <= pred_next_pc;
                end
            end
        end

        // ---- main-memory read-fill controller ----
        if (mbusy) begin
            mbusy <= 1'b0;
        end else if (d_miss) begin
            mbusy <= 1'b1; mfi <= 1'b0; mfa <= m_addr;   // D-fill (priority)
        end else if (fetch_active & ifetch_stall) begin
            mbusy <= 1'b1; mfi <= 1'b1; mfa <= pc;       // I-fill
        end
    end
endmodule

// Branch predictor: a table of 2-bit saturating counters indexed by the low
// bits of the PC (a bimodal predictor). Mirrors the Ivy sub-isolate cpu.bp.
// Predicts taken when the indexed counter is in a taken state (2 or 3); on a
// resolved branch it nudges the counter toward the outcome, saturating at 0/3.
// The bht has no reset (init-only in Ivy), which is irrelevant to the inductive
// equivalence check.
module bp (
    \posedge ,
    rst,
    fetch_pc,
    br_valid,
    br_pc,
    br_taken,
    predicted_taken
);
    input \posedge ;
    input rst;
    input [7:0] fetch_pc;      // PC being fetched (to predict)
    input br_valid;            // a conditional branch resolves this cycle
    input [7:0] br_pc;         // the resolving branch's PC
    input br_taken;            // its true outcome
    output predicted_taken;    // the prediction for fetch_pc

    reg [1:0] bht [0:15];

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
