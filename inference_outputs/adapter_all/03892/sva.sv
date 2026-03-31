module bin_counter_sva (
    input logic clk,
    input logic reset,
    input logic enable,
    input logic [3:0] count
);

    // Reset forces count to zero.
    check_reset_clears_count: assert property (
        @(posedge clk) reset |-> (count == 4'b0000)
    );

    // Reset has priority over enable.
    check_reset_priority_over_enable: assert property (
        @(posedge clk) (reset && enable) |-> (count == 4'b0000)
    );

    // When enabled outside reset, count increments by one.
    check_count_increments_when_enabled: assert property (
        @(posedge clk) disable iff (reset) enable |-> (count == ($past(count) + 4'd1))
    );

    // When disabled outside reset, count holds its value.
    check_count_holds_when_disabled: assert property (
        @(posedge clk) disable iff (reset) !enable |-> (count == $past(count))
    );

    // Count wraps from 15 back to 0 when enabled.
    check_count_wraps_from_max: assert property (
        @(posedge clk) disable iff (reset) (enable && (count == 4'hF)) |-> (count == 4'h0)
    );

endmodule