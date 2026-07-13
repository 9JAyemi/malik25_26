module up_counter_sva (
    input logic clk,
    input logic reset,
    input logic [3:0] count,
    input logic out
);

    // Reset clears the counter and the output on the next clock.
    check_reset_clears_state: assert property (
        @(posedge clk) reset |=> (count == 4'h0 && out == 1'b0)
    );

    // The counter increments by one when reset is low.
    check_count_increments: assert property (
        @(posedge clk) disable iff (reset) 1'b1 |=> (count == ($past(count) + 4'd1))
    );

    // The counter wraps from 15 back to 0.
    check_count_wraps: assert property (
        @(posedge clk) disable iff (reset) (count == 4'hF) |=> (count == 4'h0)
    );

    // The output toggles when reset is low.
    check_out_toggles: assert property (
        @(posedge clk) disable iff (reset) 1'b1 |=> (out == ~$past(out))
    );

    // The output is the inverse of the previous cycle's reset.
    check_out_matches_prev_reset: assert property (
        @(posedge clk) 1'b1 |=> (out == ~$past(reset))
    );

endmodule