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

// When enabled, the counter increments by one on the next clock.
    check_count_increments_when_enabled: assert property (
        @(posedge clk) disable iff (reset) enable |=> (count == ($past(count) + 2'd1))
    );

// When not enabled, the counter holds its value on the next clock.
    check_count_holds_when_disabled: assert property (
        @(posedge clk) disable iff (reset) !enable |=> (count == $past(count))
    );

// The 2-bit counter wraps from 3 to 0 when enabled.
    check_count_wraps_from_max: assert property (
        @(posedge clk) disable iff (reset) (enable && (count == 2'b11)) |=> (count == 2'b00)
    );

endmodule
