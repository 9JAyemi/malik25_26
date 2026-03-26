module counter_sva (
    input logic       clk,
    input logic       rst,
    input logic [3:0] out
);

    // A reset cycle clears the counter to zero on the following clock.
    check_reset_clears_out: assert property (
        @(posedge clk) disable iff ($initstate)
        rst |=> (out == 4'b0000)
    );

    // On the first non-reset cycle after reset, the observed count is zero.
    check_post_reset_zero: assert property (
        @(posedge clk) disable iff (rst || $initstate)
        $past(rst) |-> (out == 4'b0000)
    );

    // In normal operation, the counter increments by one each clock.
    check_counter_increments: assert property (
        @(posedge clk) disable iff (rst || $initstate)
        !$past(rst) |-> (out == ($past(out) + 4'd1))
    );

    // The 4-bit counter wraps from 15 back to 0.
    check_counter_wraps: assert property (
        @(posedge clk) disable iff (rst || $initstate)
        (!$past(rst) && ($past(out) == 4'hF)) |-> (out == 4'h0)
    );

endmodule