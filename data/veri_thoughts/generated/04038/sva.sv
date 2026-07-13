module up_counter_sva (
    input logic        reset,
    input logic        clk,
    input logic [15:0] q
);

    // q is zero on the first cycle after a reset cycle.
    check_q_zero_after_reset: assert property (
        @(posedge clk) disable iff (reset || $initstate)
        $past(reset) |-> (q == 16'd0)
    );

    // q increments by one across consecutive non-reset cycles.
    check_q_increments_each_cycle: assert property (
        @(posedge clk) disable iff (reset || $initstate)
        !$past(reset) |-> (q == ($past(q) + 16'd1))
    );

    // A non-reset increment from all ones wraps q to zero.
    check_q_wraps_from_max: assert property (
        @(posedge clk) disable iff (reset || $initstate)
        (!$past(reset) && ($past(q) == 16'hFFFF)) |-> (q == 16'd0)
    );

    // A non-reset increment below the maximum increases q.
    check_q_increases_below_max: assert property (
        @(posedge clk) disable iff (reset || $initstate)
        (!$past(reset) && ($past(q) != 16'hFFFF)) |-> (q > $past(q))
    );

endmodule