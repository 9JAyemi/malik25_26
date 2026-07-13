module pipelined_or_gate_sva (
    input logic a,
    input logic b,
    input logic clk,
    input logic reset,
    input logic out,
    input logic stage1_out,
    input logic stage2_out
);
    // Clock: clk (posedge). Reset: reset (active-high, async in RTL). Logic: sequential 3-stage pipeline (stage1_out<=a|b, stage2_out<=stage1_out, out<=stage2_out).

    // On any clock where reset is HIGH, all pipeline registers are 0.
    check_reset_clears_pipeline: assert property (
        @(posedge clk) reset |-> (stage1_out == 1'b0) && (stage2_out == 1'b0) && (out == 1'b0)
    );

    // stage1_out equals OR of inputs from previous cycle when prior cycle wasn't in reset.
    check_stage1_captures_or_prev: assert property (
        @(posedge clk) disable iff (reset) !$past(reset) |-> (stage1_out == ($past(a) | $past(b)))
    );

    // stage2_out equals prior cycle's stage1_out when prior cycle wasn't in reset.
    check_stage2_captures_stage1_prev: assert property (
        @(posedge clk) disable iff (reset) !$past(reset) |-> (stage2_out == $past(stage1_out))
    );

    // out equals prior cycle's stage2_out when prior cycle wasn't in reset.
    check_out_captures_stage2_prev: assert property (
        @(posedge clk) disable iff (reset) !$past(reset) |-> (out == $past(stage2_out))
    );

    // stage2_out equals OR of inputs from previous cycle when prior cycle wasn't in reset.
    check_stage2_captures_or_prev: assert property (
        @(posedge clk) disable iff (reset) !$past(reset) |-> (stage2_out == ($past(a) | $past(b)))
    );

    // out equals OR of inputs from two cycles earlier when last two cycles weren't in reset.
    check_out_two_cycle_or: assert property (
        @(posedge clk) disable iff (reset) (!$past(reset,1) && !$past(reset,2)) |-> (out == ($past(a,2) | $past(b,2)))
    );

    // One cycle after a reset cycle, all pipeline registers are still 0 before new updates.
    check_one_cycle_after_reset_holds_zero: assert property (
        @(posedge clk) disable iff (reset) $past(reset) |-> (stage1_out == 1'b0) && (stage2_out == 1'b0) && (out == 1'b0)
    );
endmodule