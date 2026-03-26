module counter_sva (
    input logic       clk,
    input logic       rst,
    input logic [3:0] count
);

    // Reset clears the counter on the next clocked state.
    check_reset_clears_count: assert property (
        @(posedge clk) rst |=> (count == 4'b0000)
    );

    // When not in reset, the counter increments by one each cycle.
    check_count_increments: assert property (
        @(posedge clk) disable iff (rst)
        1'b1 |=> (count == ($past(count) + 4'd1))
    );

    // When not in reset, the counter wraps from 15 back to 0.
    check_count_wraps: assert property (
        @(posedge clk) disable iff (rst)
        (count == 4'hF) |=> (count == 4'h0)
    );

endmodule