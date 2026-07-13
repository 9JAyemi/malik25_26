module binary_counter_sva (
    input logic       clk,
    input logic       rst,
    input logic [3:0] out
);

    // While reset is low, the counter output is zero.
    check_reset_clears_out: assert property (
        @(posedge clk) !rst |-> (out == 4'b0000)
    );

    // After a clock sampled in reset, the next sampled value is still zero.
    check_reset_release_starts_from_zero: assert property (
        @(posedge clk) !rst |=> (out == 4'b0000)
    );

    // For counts below 15, the counter increments by one on the next clock.
    check_counter_increments: assert property (
        @(posedge clk) disable iff (!rst)
        (out != 4'hF) |=> (out == ($past(out) + 4'h1))
    );

    // When the counter reaches 15, it wraps back to zero on the next clock.
    check_counter_wraps: assert property (
        @(posedge clk) disable iff (!rst)
        (out == 4'hF) |=> (out == 4'b0000)
    );

endmodule