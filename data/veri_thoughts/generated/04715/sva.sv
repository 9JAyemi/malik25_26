module counter_4bit_sva(
    input logic clk,
    input logic reset,
    input logic enable,
    input logic [3:0] count
);

    // Reset drives count to zero on the next sampled cycle.
    check_reset_clears_count: assert property (
        @(posedge clk) reset |=> (count == 4'b0000)
    );

    // Reset has priority over enable when both are high.
    check_reset_priority_over_enable: assert property (
        @(posedge clk) (reset && enable) |=> (count == 4'b0000)
    );

    // When enabled outside reset, count increments by one.
    check_increment_on_enable: assert property (
        @(posedge clk) disable iff (reset)
        enable |=> (count == ($past(count) + 4'd1))
    );

    // When disabled outside reset, count holds its value.
    check_hold_when_disabled: assert property (
        @(posedge clk) disable iff (reset)
        !enable |=> (count == $past(count))
    );

    // Enabling at 4'hf wraps the counter back to zero.
    check_wrap_from_max: assert property (
        @(posedge clk) disable iff (reset)
        (enable && (count == 4'hf)) |=> (count == 4'h0)
    );

endmodule