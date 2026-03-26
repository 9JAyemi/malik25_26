module counter_sva (
    input logic       clk,
    input logic       rst,
    input logic [3:0] count
);

    // clk is the only clock; rst is an active-high synchronous reset.

    // A reset cycle clears count to zero.
    check_reset_clears_count: assert property (
        @(posedge clk) rst |=> (count == 4'h0)
    );

    // On each non-reset cycle, count increments by one on the next cycle.
    check_count_increments: assert property (
        @(posedge clk) disable iff (rst) 1'b1 |=> (count == ($past(count) + 4'h1))
    );

    // A maximum count value rolls over to zero on the next non-reset cycle.
    check_count_rollover: assert property (
        @(posedge clk) disable iff (rst) (count == 4'hF) |=> (count == 4'h0)
    );

endmodule