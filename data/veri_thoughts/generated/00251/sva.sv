module binary_counter_sva (
    input logic       clk,
    input logic       reset,
    input logic [3:0] count
);

    // A sampled reset must leave the counter at zero by the next clock.
    check_reset_clears_count: assert property (
        @(posedge clk) reset |=> (count == 4'b0000)
    );

    // Between non-reset samples, count can only advance by one or be cleared to zero.
    check_count_transition_is_increment_or_zero: assert property (
        @(posedge clk) disable iff (reset)
        1'b1 |=> ((count == ($past(count) + 4'd1)) || (count == 4'b0000))
    );

    // A sampled maximum count must wrap to zero on the next sample.
    check_wraps_after_max: assert property (
        @(posedge clk) disable iff (reset)
        1'b1 |=> (($past(count) != 4'hF) || (count == 4'h0))
    );

    // From a sampled zero, the next nonzero value can only be one.
    check_zero_advances_to_one: assert property (
        @(posedge clk) disable iff (reset)
        1'b1 |=> (($past(count) != 4'h0) || (count == 4'h0) || (count == 4'h1))
    );

endmodule