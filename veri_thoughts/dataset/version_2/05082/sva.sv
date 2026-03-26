module binary_counter_sva(
    input logic       clk,
    input logic       reset,
    input logic [3:0] count
);

    // Reset forces the counter to zero on the next clock.
    check_reset_clears_count: assert property (
        @(posedge clk) disable iff ($initstate)
        reset |=> (count == 4'b0000)
    );

    // When not in reset, the counter increments by one each clock.
    check_count_increments: assert property (
        @(posedge clk) disable iff (reset || $initstate)
        !reset |=> (count == ($past(count) + 4'd1))
    );

    // The 4-bit counter wraps from 15 back to 0.
    check_count_wraps_from_max: assert property (
        @(posedge clk) disable iff (reset || $initstate)
        (!reset && (count == 4'hF)) |=> (count == 4'h0)
    );

    // On the first cycle after reset deasserts, the counter is still zero.
    check_zero_on_reset_release: assert property (
        @(posedge clk) disable iff (reset || $initstate)
        $past(reset) |-> (count == 4'b0000)
    );

endmodule