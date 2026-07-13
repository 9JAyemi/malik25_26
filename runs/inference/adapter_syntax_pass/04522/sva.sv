module binary_counter_sva (
    input logic clk,
    input logic reset,
    input logic [3:0] count
);

    // Reset forces the counter to zero.
    check_reset_clears_count: assert property (
        @(posedge clk) reset |-> (count == 4'h0)
    );

    // A terminal count wraps back to zero on the next clock.
    check_wrap_from_max: assert property (
        @(posedge clk) disable iff (reset)
        (count == 4'hF) |=> (count == 4'h0)
    );

    // Non-terminal counts increment by one on the next clock.
    check_increment_from_nonmax: assert property (
        @(posedge clk) disable iff (reset)
        (count != 4'hF) |=> (count == ($past(count) + 4'h1))
    );

    // The counter value is always zero or one more than the previous value.
    check_count_progression: assert property (
        @(posedge clk) disable iff (reset)
        1'b1 |=> ((count == 4'h0) || (count == ($past(count) + 4'h1)))
    );

endmodule