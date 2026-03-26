module sync_counter_sva (
    input logic       clk,
    input logic       reset,
    input logic [3:0] count
);

    // Reset forces count to zero by the next sampled cycle.
    check_reset_clears_count: assert property (
        @(posedge clk) reset |=> (count == 4'b0000)
    );

    // Count is zero on the cycle reset is released.
    check_count_zero_when_reset_releases: assert property (
        @(posedge clk) disable iff (reset) $fell(reset) |-> (count == 4'b0000)
    );

    // Without reset, count increments by one every cycle.
    check_count_increments_without_reset: assert property (
        @(posedge clk) disable iff (reset) 1'b1 |=> (count == ($past(count) + 4'd1))
    );

    // A maximum count value rolls over to zero.
    check_count_rolls_over_from_max: assert property (
        @(posedge clk) disable iff (reset) (count == 4'hF) |=> (count == 4'h0)
    );

    // After reset release, the first active count value becomes one.
    check_first_increment_after_reset_release: assert property (
        @(posedge clk) disable iff (reset) $fell(reset) |=> (count == 4'h1)
    );

endmodule