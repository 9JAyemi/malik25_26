module counter_with_sum_sva (
    input logic       clk,
    input logic       reset,
    input logic [3:0] input1,
    input logic [3:0] input2,
    input logic [3:0] sum,
    input logic [3:0] counter_out
);

    // A sampled reset clears the counter by the next clock.
    check_counter_clears_after_reset: assert property (
        @(posedge clk) reset |=> (counter_out == 4'h0)
    );

    // A sampled reset clears the stored input2, so sum matches input1 next cycle.
    check_sum_matches_input1_after_reset: assert property (
        @(posedge clk) reset |=> (sum == input1)
    );

    // From any non-maximum value, the counter increments on the next active cycle.
    check_counter_increments_from_non_max: assert property (
        @(posedge clk) disable iff (reset)
        (counter_out != 4'hF) |=> (counter_out == ($past(counter_out) + 4'h1))
    );

    // From 4'hF, the counter wraps to zero on the next active cycle.
    check_counter_wraps_from_max: assert property (
        @(posedge clk) disable iff (reset)
        (counter_out == 4'hF) |=> (counter_out == 4'h0)
    );

    // On active cycles, sum uses the current input1 and the previous cycle's input2.
    check_sum_uses_previous_input2: assert property (
        @(posedge clk) disable iff (reset)
        1'b1 |=> (sum == (input1 + $past(input2)))
    );

endmodule