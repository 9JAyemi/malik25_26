module up_counter_sva (
    input logic       CLK,
    input logic       CLR,
    input logic [3:0] Q
);

    // Reset clears the counter on the following clock sample.
    check_reset_clears_q: assert property (
        @(posedge CLK)
        CLR |=> (Q == 4'h0)
    );

    // After reset is released, the counter value is zero.
    check_zero_after_reset_release: assert property (
        @(posedge CLK) disable iff (CLR || $initstate)
        $past(CLR) |-> (Q == 4'h0)
    );

    // In non-reset cycles, the counter increments by one until it reaches 15.
    check_counts_up_during_run: assert property (
        @(posedge CLK) disable iff (CLR || $initstate)
        (!$past(CLR) && ($past(Q) != 4'hF)) |-> (Q == ($past(Q) + 4'd1))
    );

    // The 4-bit counter wraps from 15 back to 0.
    check_wraps_from_max: assert property (
        @(posedge CLK) disable iff (CLR || $initstate)
        (!$past(CLR) && ($past(Q) == 4'hF)) |-> (Q == 4'h0)
    );

endmodule