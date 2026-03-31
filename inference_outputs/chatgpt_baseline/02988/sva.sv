module RegisterAdd_4_sva (
    input logic CLK,
    input logic reset,
    input logic [3:0] in1,
    input logic [3:0] in2,
    input logic [3:0] out
);
    // If reset is 1 on this edge, out must be 0 on the next edge.
    check_reset_clears_out_next: assert property (
        @(posedge CLK) reset |=> (out == 4'd0)
    );

    // If reset was 1 in the previous cycle, out must be 0 now.
    check_prev_reset_out_zero_now: assert property (
        @(posedge CLK) $past(reset) |-> (out == 4'd0)
    );

    // If not in reset for two consecutive cycles, out equals in1+in2 from the prior cycle.
    check_sum_update_two_cycle_nonreset: assert property (
        @(posedge CLK) disable iff (reset) (!reset ##1 !reset) |-> (out == $past(in1 + in2))
    );

    // On the cycle reset deasserts, out must be 0 (was cleared by prior reset cycle).
    check_out_zero_on_reset_deassert: assert property (
        @(posedge CLK) $fell(reset) |-> (out == 4'd0)
    );

    // In normal operation (previous cycle not reset), out equals previous cycle's in1+in2.
    check_sum_update_prev_not_reset: assert property (
        @(posedge CLK) disable iff (reset) $past(!reset) |-> (out == $past(in1 + in2))
    );
endmodule