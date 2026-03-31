module counter_sva (
    input logic clk,
    input logic reset,
    input logic enable,
    input logic [1:0] count
);

    // Reset clears the counter on the next clock.
    check_reset_clears_count: assert property (
        @(posedge clk) reset |=> (count == 2'b00)
    );

    // Reset has priority over enable.
    check_reset_priority_over_enable: assert property (
        @(posedge clk) (reset && enable) |=> (count == 2'b00)
    );

    // Enable increments the counter by one when not in reset.
    check_enable_increments_count: assert property (
        @(posedge clk) disable iff (reset) enable |=> (count == ($past(count) + 2'b01))
    );

    // The counter holds its value when enable is low.
    check_disable_holds_count: assert property (
        @(posedge clk) disable iff (reset) !enable |=> (count == $past(count))
    );

    // The counter wraps from 2'b11 back to 2'b00 when enabled.
    check_wrap_from_max: assert property (
        @(posedge clk) disable iff (reset) (enable && (count == 2'b11)) |=> (count == 2'b00)
    );

endmodule