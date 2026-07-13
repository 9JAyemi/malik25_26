module counter_4bit_sva (
    input logic clk,
    input logic reset,          // active-LOW asynchronous reset
    input logic [3:0] count
);

    ///// Reset behavior /////
    // While reset is LOW, count must be 0.
    check_count_zero_while_reset_low: assert property (
        @(posedge clk) (reset == 1'b0) |-> (count == 4'd0)
    );

    // If reset stays LOW across consecutive clocks, count remains 0.
    check_count_zero_on_consecutive_reset_low: assert property (
        @(posedge clk) ($past(reset) == 1'b0 && reset == 1'b0) |-> (count == 4'd0)
    );

    // On reset deassertion (0->1) at a clock edge, count becomes 1.
    check_count_one_on_reset_rise: assert property (
        @(posedge clk) $rose(reset) |-> (count == 4'd1)
    );

    // On reset deassertion (0->1), the previous sampled count was 0.
    check_past_count_zero_on_reset_rise: assert property (
        @(posedge clk) $rose(reset) |-> ($past(count) == 4'd0)
    );

    ///// General invariants /////
    // Count value remains within 4-bit range during normal operation.
    check_count_range_when_not_in_reset: assert property (
        @(posedge clk) disable iff (!reset) (count inside {[4'd0:4'd15]})
    );

endmodule