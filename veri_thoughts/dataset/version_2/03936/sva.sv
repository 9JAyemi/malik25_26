module binary_up_counter_sva (
    input logic       clk,
    input logic       reset,
    input logic       enable,
    input logic [3:0] count
);

    // Reset clears the counter to zero on the next clock.
    check_reset_clears_count: assert property (
        @(posedge clk) reset |=> (count == 4'h0)
    );

    // When disabled without reset, the counter holds its value.
    check_hold_when_disabled: assert property (
        @(posedge clk) disable iff (reset)
        (!enable) |=> (count == $past(count))
    );

    // When enabled below max, the counter increments by one.
    check_increment_when_enabled: assert property (
        @(posedge clk) disable iff (reset)
        (enable && (count != 4'hF)) |=> (count == ($past(count) + 4'h1))
    );

    // When enabled at max, the counter wraps back to zero.
    check_wrap_when_max: assert property (
        @(posedge clk) disable iff (reset)
        (enable && (count == 4'hF)) |=> (count == 4'h0)
    );

endmodule