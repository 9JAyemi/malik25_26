module up_counter_sva (
    input logic clk,
    input logic reset,
    input logic [3:0] count,
    input logic out
);

    // Reset clears both count and out on the next clock.
    check_reset_clears_outputs: assert property (
        @(posedge clk) reset |=> (count == 4'b0000 && out == 1'b0)
    );

    // When not in reset, count increments by one on the next clock.
    check_count_increments: assert property (
        @(posedge clk) disable iff (reset) 1'b1 |=> (count == ($past(count) + 4'd1))
    );

    // When not in reset, out toggles on the next clock.
    check_out_toggles: assert property (
        @(posedge clk) disable iff (reset) 1'b1 |=> (out == ~$past(out))
    );

    // On the first cycle after reset deasserts, count is zero and out is high.
    check_reset_release_state: assert property (
        @(posedge clk) disable iff (reset) $fell(reset) |-> (count == 4'b0000 && out == 1'b1)
    );

    // On the second cycle after reset deasserts, count is one and out is low.
    check_reset_release_first_increment: assert property (
        @(posedge clk) disable iff (reset) $fell(reset) |-> ##1 (count == 4'b0001 && out == 1'b0)
    );

endmodule