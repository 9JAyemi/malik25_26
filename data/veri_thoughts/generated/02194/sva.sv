module three_stage_pipeline_sva (
    input logic clk,
    input logic reset,
    input logic [19:0] b,
    input logic [19:0] c,
    input logic [19:0] d,
    input logic [19:0] q,
    input logic [19:0] r_b,
    input logic [19:0] r_e,
    input logic [19:0] r_c,
    input logic [19:0] rr_e,
    input logic [19:0] rr_b,
    input logic [19:0] r_qx
);
    // Clock: clk (posedge). Reset: reset (active-high synchronous). Three-stage sequential pipeline.

    ///// Reset behavior ///// 
    // After a reset cycle, stage-1 regs clear to zero on the next clock.
    reset_clears_stage1: assert property (
        @(posedge clk) reset |=> (r_b == 20'b0) && (r_e == 20'b0)
    );
    // After a reset cycle, stage-2 regs clear to zero on the next clock.
    reset_clears_stage2: assert property (
        @(posedge clk) reset |=> (r_c == 20'b0) && (rr_e == 20'b0) && (rr_b == 20'b0)
    );
    // After a reset cycle, stage-3 reg and output clear to zero on the next clock.
    reset_clears_stage3_and_q: assert property (
        @(posedge clk) reset |=> (r_qx == 20'b0) && (q == 20'b0)
    );
    // If reset is held for consecutive cycles, all pipeline regs and q remain zero.
    hold_zero_while_reset: assert property (
        @(posedge clk) (reset && $past(reset)) |-> (r_b==20'b0) && (r_e==20'b0) && (r_c==20'b0) && (rr_e==20'b0) && (rr_b==20'b0) && (r_qx==20'b0) && (q==20'b0)
    );

    ///// Data movement between stages /////
    // q is a direct reflection of r_qx.
    q_matches_r_qx: assert property (
        @(posedge clk) disable iff (reset) q == r_qx
    );
    // Stage-1: r_b captures d from the previous cycle (when previous cycle was not reset).
    load_r_b_from_d: assert property (
        @(posedge clk) disable iff (reset) $past(!reset) |-> (r_b == $past(d))
    );
    // Stage-1: r_e captures r_qx from the previous cycle (when previous cycle was not reset).
    load_r_e_from_r_qx: assert property (
        @(posedge clk) disable iff (reset) $past(!reset) |-> (r_e == $past(r_qx))
    );
    // Stage-2: r_c captures c from the previous cycle (when previous cycle was not reset).
    load_r_c_from_c: assert property (
        @(posedge clk) disable iff (reset) $past(!reset) |-> (r_c == $past(c))
    );
    // Stage-2: rr_b captures r_b from the previous cycle (when previous cycle was not reset).
    load_rr_b_from_r_b: assert property (
        @(posedge clk) disable iff (reset) $past(!reset) |-> (rr_b == $past(r_b))
    );
    // Stage-2: rr_e captures r_e from the previous cycle (when previous cycle was not reset).
    load_rr_e_from_r_e: assert property (
        @(posedge clk) disable iff (reset) $past(!reset) |-> (rr_e == $past(r_e))
    );
    // Stage-3: r_qx captures bitwise AND of rr_b, r_c, rr_e from the previous cycle (when previous cycle was not reset).
    compute_r_qx_from_prev: assert property (
        @(posedge clk) disable iff (reset) $past(!reset) |-> (r_qx == $past(rr_b & r_c & rr_e))
    );
endmodule