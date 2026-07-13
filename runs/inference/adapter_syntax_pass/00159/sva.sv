module top_module_sva (
    input logic clk,
    input logic reset,
    input logic [3:0] q
);

    // Reset forces the counter to zero.
    check_reset_clears_q: assert property (
        @(posedge clk) reset |-> (q == 4'b0000)
    );

    // A terminal count wraps back to zero.
    check_wrap_from_max: assert property (
        @(posedge clk) disable iff (reset)
        (q == 4'b1111) |=> (q == 4'b0000)
    );

    // A non-terminal count increments by one.
    check_increment_from_nonmax: assert property (
        @(posedge clk) disable iff (reset)
        (q != 4'b1111) |=> (q == ($past(q) + 4'b0001))
    );

    // The counter value is always zero or one more than the previous value.
    check_q_is_zero_or_incremented: assert property (
        @(posedge clk) disable iff (reset)
        1'b1 |=> ((q == 4'b0000) || (q == ($past(q) + 4'b0001)))
    );

endmodule