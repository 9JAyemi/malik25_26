module binary_counter_sva (
    input logic clk,
    input logic reset,
    input logic load,
    input logic [3:0] target,
    input logic [3:0] count,
    input logic equal
);

    // After a non-reset load cycle, count takes the previous target value.
    check_load_updates_count: assert property (
        @(posedge clk) disable iff (reset || $initstate)
        $past(!reset && load) |-> (count == $past(target))
    );

    // Without reset or load, count increments from non-maximum values.
    check_increments_from_nonmax: assert property (
        @(posedge clk) disable iff (reset || $initstate)
        ($past(!reset && !load) && ($past(count) != 4'hF)) |-> (count == ($past(count) + 4'd1))
    );

    // Without reset or load, count wraps from 4'hF to 4'h0.
    check_wraps_after_max: assert property (
        @(posedge clk) disable iff (reset || $initstate)
        ($past(!reset && !load) && ($past(count) == 4'hF)) |-> (count == 4'h0)
    );

    // On the first non-reset cycle after reset, count is zero.
    check_reset_release_clears_count: assert property (
        @(posedge clk) disable iff (reset || $initstate)
        $past(reset) |-> (count == 4'h0)
    );

    // equal is high when count matches target.
    check_equal_high_on_match: assert property (
        @(posedge clk) disable iff (reset || $initstate)
        (count == target) |-> (equal == 1'b1)
    );

    // equal is low when count differs from target.
    check_equal_low_on_mismatch: assert property (
        @(posedge clk) disable iff (reset || $initstate)
        (count != target) |-> (equal == 1'b0)
    );

endmodule