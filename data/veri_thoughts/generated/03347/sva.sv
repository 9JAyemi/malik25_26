module counter_sva (
    input logic       clk,
    input logic       reset,
    input logic       enable,
    input logic [3:0] count
);

    // Reset clears the counter on the next clock.
    check_reset_clears_count: assert property (
        @(posedge clk) reset |=> (count == 4'b0000)
    );

    // Reset takes priority over enable.
    check_reset_overrides_enable: assert property (
        @(posedge clk) (reset && enable) |=> (count == 4'b0000)
    );

    // When enabled below max, the counter increments by one.
    check_count_increments_below_max: assert property (
        @(posedge clk) disable iff (reset)
        (enable && (count != 4'hF)) |=> (count == ($past(count) + 4'd1))
    );

    // When enabled at max, the counter wraps to zero.
    check_count_wraps_at_max: assert property (
        @(posedge clk) disable iff (reset)
        (enable && (count == 4'hF)) |=> (count == 4'h0)
    );

    // When not enabled, the counter holds its value.
    check_count_holds_when_disabled: assert property (
        @(posedge clk) disable iff (reset)
        (!enable) |=> (count == $past(count))
    );

endmodule