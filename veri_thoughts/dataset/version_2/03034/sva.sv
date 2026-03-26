module up_counter_sva (
    input logic       clock,
    input logic       reset,
    input logic [3:0] out
);

    // A high reset drives the counter to zero on the next clock.
    check_reset_clears_out: assert property (
        @(posedge clock) reset |=> (out == 4'b0000)
    );

    // On the first cycle after reset deasserts, the sampled counter value is zero.
    check_post_reset_zero: assert property (
        @(posedge clock) reset ##1 !reset |-> (out == 4'b0000)
    );

    // When not at 4'hF, the counter increments by one each cycle.
    check_count_increments: assert property (
        @(posedge clock) disable iff (reset)
        (out != 4'hF) |=> (out == ($past(out) + 4'd1))
    );

    // When at 4'hF, the counter wraps back to zero on the next cycle.
    check_count_wraps: assert property (
        @(posedge clock) disable iff (reset)
        (out == 4'hF) |=> (out == 4'h0)
    );

endmodule