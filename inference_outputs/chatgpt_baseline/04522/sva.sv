module binary_counter_assertions (
    input logic       clk,
    input logic       reset,
    input logic [3:0] count
);

    // A sampled reset leaves the counter cleared by the next clock.
    check_reset_clears_by_next_clock: assert property (
        @(posedge clk) reset |=> (count == 4'b0000)
    );

    // Reset deassertion is observed with count still at zero.
    check_reset_release_sees_zero: assert property (
        @(posedge clk) reset ##1 !reset |-> (count == 4'b0000)
    );

    // From 15, the counter wraps back to zero.
    check_wrap_from_fifteen: assert property (
        @(posedge clk) disable iff (reset)
            (count == 4'b1111) |=> (count == 4'b0000)
    );

    // On non-reset cycles, the next sampled count is zero or increments by one.
    check_count_progression: assert property (
        @(posedge clk) disable iff (reset)
            1'b1 |=> ((count == 4'b0000) || (count == ($past(count) + 4'b0001)))
    );

endmodule