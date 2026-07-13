module counter_sva (
    input logic       clk,
    input logic       rst,
    input logic [3:0] count
);

    // Count matches the previous cycle's reset-or-increment update.
    check_count_state_update: assert property (
        @(posedge clk)
        !$initstate |-> (count == ($past(rst) ? 4'b0000 : ($past(count) + 4'b0001)))
    );

    // A reset cycle drives count to zero on the next sampled cycle.
    check_reset_clears_count: assert property (
        @(posedge clk)
        rst |=> (count == 4'b0000)
    );

    // After a reset cycle, the first cycle out of reset still shows zero.
    check_count_zero_after_reset: assert property (
        @(posedge clk) disable iff (rst)
        (!$initstate && $past(rst)) |-> (count == 4'b0000)
    );

    // In consecutive non-reset cycles, count increments by one modulo 16.
    check_count_increments: assert property (
        @(posedge clk) disable iff (rst)
        (!$initstate && !$past(rst)) |-> (count == ($past(count) + 4'b0001))
    );

endmodule