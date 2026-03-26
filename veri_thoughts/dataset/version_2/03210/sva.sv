module binary_counter_sva (
    input logic       clk,
    input logic       rst_n,
    input logic [3:0] Q
);

    // Sequential 4-bit counter with an active-low asynchronous reset.

    // When reset is asserted, the counter state is zero.
    check_reset_clears_q: assert property (
        @(posedge clk) !rst_n |-> (Q == 4'b0000)
    );

    // The sampled state remains zero on the first clock after a sampled reset cycle.
    check_sample_after_reset_is_zero: assert property (
        @(posedge clk) disable iff (!rst_n || $initstate)
        !$past(rst_n) |-> (Q == 4'b0000)
    );

    // Across consecutive sampled active cycles, the counter either increments or has been asynchronously cleared to zero.
    check_count_advances_or_async_clears: assert property (
        @(posedge clk) disable iff (!rst_n || $initstate)
        $past(rst_n) |-> ((Q == ($past(Q) + 4'd1)) || (Q == 4'b0000))
    );

    // Any nonzero sampled count must come from a one-step increment with reset high in the prior cycle.
    check_nonzero_values_come_from_increment: assert property (
        @(posedge clk) disable iff (!rst_n || $initstate)
        (Q != 4'b0000) |-> ($past(rst_n) && (Q == ($past(Q) + 4'd1)))
    );

    // A sampled count of one must follow a sampled count of zero.
    check_one_follows_zero: assert property (
        @(posedge clk) disable iff (!rst_n || $initstate)
        (Q == 4'b0001) |-> ($past(rst_n) && ($past(Q) == 4'b0000))
    );

endmodule