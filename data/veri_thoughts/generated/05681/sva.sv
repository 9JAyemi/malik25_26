module binary_counter_sva (
    input logic        clk,
    input logic        reset,
    input logic [15:0] count
);

    // A reset cycle clears the counter by the next clock.
    check_reset_clears_count: assert property (
        @(posedge clk) reset |=> (count == 16'h0000)
    );

    // While reset stays asserted, the sampled count remains zero.
    check_reset_holds_count_zero: assert property (
        @(posedge clk) (reset && $past(reset)) |-> (count == 16'h0000)
    );

    // The first non-reset cycle after reset still shows zero.
    check_post_reset_count_zero: assert property (
        @(posedge clk) disable iff (reset) $past(reset) |-> (count == 16'h0000)
    );

    // Outside reset, the counter increments by one every cycle.
    check_count_increments: assert property (
        @(posedge clk) disable iff (reset) !$past(reset) |-> (count == ($past(count) + 16'h0001))
    );

    // The 16-bit counter wraps from all ones back to zero.
    check_count_wraps: assert property (
        @(posedge clk) disable iff (reset) (!$past(reset) && ($past(count) == 16'hFFFF)) |-> (count == 16'h0000)
    );

endmodule