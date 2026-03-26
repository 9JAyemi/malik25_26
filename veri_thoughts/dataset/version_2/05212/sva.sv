module binary_counter_assertions (
    input logic [3:0] q,
    input logic       clk,
    input logic       rst
);

    // 4-bit up-counter on posedge clk with active-high synchronous reset.

    // Synchronous reset clears the counter.
    check_sync_reset_clears_q: assert property (
        @(posedge clk) rst |=> (q == 4'b0000)
    );

    // While reset stays asserted, the sampled counter value remains zero.
    check_reset_holds_q_zero: assert property (
        @(posedge clk) (rst && $past(rst)) |-> (q == 4'b0000)
    );

    // On reset release, the sampled counter value is still zero.
    check_reset_release_starts_from_zero: assert property (
        @(posedge clk) disable iff (rst) $fell(rst) |-> (q == 4'b0000)
    );

    // When below 15, the counter increments by one.
    check_counter_increments: assert property (
        @(posedge clk) disable iff (rst) (q != 4'b1111) |=> (q == ($past(q) + 4'b0001))
    );

    // When at 15, the counter wraps back to zero.
    check_counter_wraps: assert property (
        @(posedge clk) disable iff (rst) (q == 4'b1111) |=> (q == 4'b0000)
    );

endmodule