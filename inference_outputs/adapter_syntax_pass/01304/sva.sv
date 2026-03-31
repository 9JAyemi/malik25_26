module binary_counter_sva (
    input logic clk,
    input logic reset,
    input logic enable,
    input logic [3:0] count
);

    // Reset clears the counter on the next clock.
    check_reset_clears_count: assert property (
        @(posedge clk) reset |=> (count == 4'b0000)
    );

    // Reset has priority over enable.
    check_reset_priority_over_enable: assert property (
        @(posedge clk) (reset && enable) |=> (count == 4'b0000)
    );

    // Enable increments the counter by one when reset is low.
    check_enable_increments_count: assert property (
        @(posedge clk) disable iff (reset) enable |=> (count == ($past(count) + 4'd1))
    );

    // The counter holds its value when enable is low.
    check_hold_when_disabled: assert property (
        @(posedge clk) disable iff (reset) !enable |=> (count == $past(count))
    );

    // The counter wraps from 15 back to 0 when enabled.
    check_wrap_from_max: assert property (
        @(posedge clk) disable iff (reset) (enable && (count == 4'hF)) |=> (count == 4'h0)
    );

endmodule