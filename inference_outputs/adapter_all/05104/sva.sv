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

    // Reset overrides enable when both are asserted.
    check_reset_priority_over_enable: assert property (
        @(posedge clk) (reset && enable) |=> (count == 2'b00)
    );

    // When enabled without reset, the counter increments by one.
    check_increment_when_enabled: assert property (
        @(posedge clk) disable iff (reset) enable |=> (count == ($past(count) + 2'b01))
    );

    // When not enabled without reset, the counter holds its value.
    check_hold_when_disabled: assert property (
        @(posedge clk) disable iff (reset) !enable |=> (count == $past(count))
    );

    // The 2-bit counter wraps from 3 back to 0.
    check_wrap_from_max: assert property (
        @(posedge clk) disable iff (reset) (enable && (count == 2'b11)) |=> (count == 2'b00)
    );

endmodule