module binary_counter_sva (
    input logic       clk,
    input logic       reset,
    input logic [3:0] count
);

    // Reset clears count on the following clock.
    check_reset_clears_count: assert property (
        @(posedge clk) reset |=> (count == 4'b0000)
    );

    // Count wraps from 9 back to 0 when not in reset.
    check_wrap_at_nine: assert property (
        @(posedge clk) disable iff (reset)
        (count == 4'b1001) |=> (count == 4'b0000)
    );

    // Count increments by one on all other non-reset cycles.
    check_increment_otherwise: assert property (
        @(posedge clk) disable iff (reset)
        (count != 4'b1001) |=> (count == ($past(count) + 4'b0001))
    );

endmodule