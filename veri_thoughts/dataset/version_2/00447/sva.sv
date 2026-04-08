module counter_top_sva(
    input logic clk,
    input logic reset,
    input logic [4:0] count,
    input logic [3:0] count1,
    input logic [3:0] count2
);

    // Both subcounters clear on the cycle after reset.
    check_subcounters_clear_after_reset: assert property (
        @(posedge clk) disable iff (reset || $initstate)
        $past(reset) |-> ((count1 == 4'd0) && (count2 == 4'd0))
    );

    // count1 increments by one when it is below 15.
    check_count1_increments_below_max: assert property (
        @(posedge clk) disable iff (reset || $initstate)
        (!$past(reset) && ($past(count1) != 4'hF)) |-> (count1 == ($past(count1) + 4'd1))
    );

    // count1 wraps from 15 back to 0.
    check_count1_wraps_at_max: assert property (
        @(posedge clk) disable iff (reset || $initstate)
        (!$past(reset) && ($past(count1) == 4'hF)) |-> (count1 == 4'h0)
    );

    // count2 increments by one when it is below 15.
    check_count2_increments_below_max: assert property (
        @(posedge clk) disable iff (reset || $initstate)
        (!$past(reset) && ($past(count2) != 4'hF)) |-> (count2 == ($past(count2) + 4'd1))
    );

    // count2 wraps from 15 back to 0.
    check_count2_wraps_at_max: assert property (
        @(posedge clk) disable iff (reset || $initstate)
        (!$past(reset) && ($past(count2) == 4'hF)) |-> (count2 == 4'h0)
    );

    // Top count stores the previous cycle's sum of count1 and count2.
    check_top_captures_previous_sum: assert property (
        @(posedge clk) disable iff (reset || $initstate)
        count == ({1'b0, $past(count1)} + {1'b0, $past(count2)})
    );

    // Equal subcounters remain equal on the next cycle.
    check_equal_subcounters_stay_equal: assert property (
        @(posedge clk) disable iff (reset || $initstate)
        ($past(count1) == $past(count2)) |-> (count1 == count2)
    );

    // Equal subcounters produce a doubled value in the top count.
    check_equal_subcounters_double_into_count: assert property (
        @(posedge clk) disable iff (reset || $initstate)
        ($past(count1) == $past(count2)) |-> (count == {$past(count1), 1'b0})
    );

    // Top count becomes zero two cycles after reset is sampled high.
    check_top_count_zero_two_cycles_after_reset: assert property (
        @(posedge clk) disable iff (reset || $initstate)
        $past(reset, 2) |-> (count == 5'd0)
    );

    // Top count never exceeds the sum range of two 4-bit counters.
    check_top_count_within_sum_range: assert property (
        @(posedge clk) disable iff (reset || $initstate)
        count <= 5'd30
    );

endmodule