module binary_counter_sva (
    input logic       clk,
    input logic       reset,
    input logic       enable,
    input logic [3:0] count_out
);

    // Reset drives the counter to zero on the following clock.
    check_reset_clears_count: assert property (
        @(posedge clk) reset |=> (count_out == 4'b0000)
    );

    // Reset has priority over enable and still clears the counter.
    check_reset_priority_over_enable: assert property (
        @(posedge clk) (reset && enable) |=> (count_out == 4'b0000)
    );

    // When enabled outside reset, the counter increments by one.
    check_count_increments_when_enabled: assert property (
        @(posedge clk) disable iff (reset)
        enable |=> (count_out == ($past(count_out) + 4'd1))
    );

    // When disabled outside reset, the counter holds its value.
    check_count_holds_when_disabled: assert property (
        @(posedge clk) disable iff (reset)
        !enable |=> (count_out == $past(count_out))
    );

    // The 4-bit counter wraps from 15 back to 0 when enabled.
    check_wraps_from_max_to_zero: assert property (
        @(posedge clk) disable iff (reset)
        (enable && (count_out == 4'hF)) |=> (count_out == 4'h0)
    );

endmodule