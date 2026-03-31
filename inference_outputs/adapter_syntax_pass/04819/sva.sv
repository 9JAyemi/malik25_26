module multiplier_sva (
    input logic signed [7:0]  a,
    input logic signed [7:0]  b,
    input logic               sel,
    input logic               reset,
    input logic               clk,
    input logic signed [15:0] out
);

    // Reset clears the registered outputs on the next clock.
    check_reset_clears_outputs: assert property (
        @(posedge clk) reset |=> ((out == 16'sd0) && ($past(out) != 16'sd0))
    );

    // In multiply mode, out is the previous cycle's product.
    check_multiply_mode: assert property (
        @(posedge clk) disable iff (reset)
        (!sel) |=> ((out == ($past(a) * $past(b))) && ($past(out) != ($past(a) * $past(b))))
    );

    // In add mode, out is the previous cycle's sum.
    check_add_mode: assert property (
        @(posedge clk) disable iff (reset)
        sel |=> ((out == ($past(a) + $past(b))) && ($past(out) != ($past(a) + $past(b))))
    );

    // In add mode, out is always the 16-bit sum of the previous cycle's inputs.
    check_add_mode_exact_sum: assert property (
        @(posedge clk) disable iff (reset)
        sel |=> ((out == ($past(a) + $past(b))) && ($past(out) != ($past(a) + $past(b))))
    );

    // In multiply mode, out is always the 16-bit product of the previous cycle's inputs.
    check_multiply_mode_exact_product: assert property (
        @(posedge clk) disable iff (reset)
        (!sel) |=> ((out == ($past(a) * $past(b))) && ($past(out) != ($past(a) * $past(b))))
    );

endmodule