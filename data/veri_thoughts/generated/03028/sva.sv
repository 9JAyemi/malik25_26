module binary_counter_sva(
    input logic       clk,
    input logic       reset,
    input logic [3:0] out
);

    // A reset cycle clears the counter to zero.
    check_reset_clears_counter: assert property (
        @(posedge clk) reset |=> (out == 4'b0000)
    );

    // After reset deasserts, the next non-reset cycle counts from zero to one.
    check_first_count_after_reset: assert property (
        @(posedge clk) disable iff (reset)
        ($past(reset) == 1'b1) |=> (out == 4'b0001)
    );

    // In consecutive non-reset cycles, the counter increments by one.
    check_counter_increments: assert property (
        @(posedge clk) disable iff (reset)
        ($past(reset) == 1'b0) |-> (out == ($past(out) + 4'd1))
    );

    // The 4-bit counter wraps from 15 back to zero.
    check_counter_wraps: assert property (
        @(posedge clk) disable iff (reset)
        (($past(reset) == 1'b0) && ($past(out) == 4'hF)) |-> (out == 4'h0)
    );

endmodule