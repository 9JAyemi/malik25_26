module counter_sva (
    input logic       clk,
    input logic       reset,
    input logic [3:0] count
);

    // Sequential-only logic on clk; reset is active high and asynchronous.
    // count is a 4-bit output that increments and wraps from 9 to 0.

    // A sampled reset forces the counter to be 0 on the next clock.
    reset_forces_zero_next: assert property (
        @(posedge clk) reset |=> (count == 4'd0)
    );

    // A sampled value of 9 wraps back to 0 on the next clock.
    wrap_from_nine: assert property (
        @(posedge clk) disable iff (reset)
        (count == 4'd9) |=> (count == 4'd0)
    );

    // Any non-9 value increments, unless an async reset pulse clears count to 0 between clocks.
    increment_or_clear_from_non_nine: assert property (
        @(posedge clk) disable iff (reset)
        (count != 4'd9) |=> ((count == ($past(count) + 4'd1)) || (count == 4'd0))
    );

endmodule