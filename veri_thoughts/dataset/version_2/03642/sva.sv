module clk_counter_sva(
    input logic       clk,
    input logic       reset,
    input logic [3:0] counter
);

    // Each sampled count is either reset-cleared to zero or increments by one.
    check_counter_advances_or_clears: assert property (
        @(posedge clk) disable iff (!reset || $initstate)
        (counter == 4'b0000) || (counter == ($past(counter) + 4'b0001))
    );

    // Any nonzero sampled count must come from incrementing the prior sampled count.
    check_nonzero_samples_increment: assert property (
        @(posedge clk) disable iff (!reset || $initstate)
        (counter != 4'b0000) |-> (counter == ($past(counter) + 4'b0001))
    );

    // A sampled maximum count must wrap to zero on the next sampled cycle.
    check_wrap_from_max_to_zero: assert property (
        @(posedge clk) disable iff (!reset || $initstate)
        ($past(counter) == 4'hF) |-> (counter == 4'h0)
    );

    // A sampled count of one can only follow a sampled count of zero.
    check_one_follows_zero: assert property (
        @(posedge clk) disable iff (!reset || $initstate)
        (counter == 4'h1) |-> ($past(counter) == 4'h0)
    );

    // A nonzero sampled count cannot directly follow a sampled maximum count.
    check_nonzero_not_after_max: assert property (
        @(posedge clk) disable iff (!reset || $initstate)
        (counter != 4'b0000) |-> ($past(counter) != 4'hF)
    );

endmodule