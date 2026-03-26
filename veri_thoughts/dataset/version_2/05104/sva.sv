module counter_sva (
    input logic       clk,
    input logic       reset,
    input logic       enable,
    input logic [1:0] count
);

    // Reset forces count to zero on the following clock.
    check_reset_clears_count: assert property (
        @(posedge clk) reset |=> (count == 2'b00)
    );

    // When enabled, count increments by one modulo 4.
    check_enable_increments_count: assert property (
        @(posedge clk) disable iff (reset)
        enable |=> (count == ($past(count) + 2'b01))
    );

    // When not enabled, count holds its previous value.
    check_disable_holds_count: assert property (
        @(posedge clk) disable iff (reset)
        !enable |=> (count == $past(count))
    );

    // A max count of 3 wraps back to 0 when enabled.
    check_wraps_from_three_to_zero: assert property (
        @(posedge clk) disable iff (reset)
        (enable && (count == 2'b11)) |=> (count == 2'b00)
    );

endmodule