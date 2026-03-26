module up_counter_4bit_sva (
    input logic [3:0] count,
    input logic       clk,
    input logic       reset
);

    // Reset clears the counter on the following clock.
    check_reset_clears_count: assert property (
        @(posedge clk) reset |=> (count == 4'b0000)
    );

    // The counter increments by one on each cycle out of reset.
    check_count_increments: assert property (
        @(posedge clk) disable iff (reset) 1'b1 |=> (count == ($past(count) + 4'd1))
    );

    // The counter wraps from 15 back to 0.
    check_count_wraps_from_max: assert property (
        @(posedge clk) disable iff (reset) (count == 4'hF) |=> (count == 4'h0)
    );

    // After reset release, the first counted value is 1.
    check_first_increment_after_reset_release: assert property (
        @(posedge clk) (reset ##1 !reset) |=> (count == 4'h1)
    );

endmodule