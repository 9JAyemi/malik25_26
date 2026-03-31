module multiplier_sva (
    input logic signed [7:0]  a,
    input logic signed [7:0]  b,
    input logic               sel,
    input logic               reset,
    input logic               clk,
    input logic signed [15:0] out
);

    // Reset clears the registered output on the next clock.
    check_reset_clears_output: assert property (
        @(posedge clk) reset |=> (out == 16'sd0)
    );

    // With sel low, the next output is the product of a and b.
    check_product_when_sel_low: assert property (
        @(posedge clk) disable iff (reset)
        !sel |=> (out == $past(a * b))
    );

    // With sel high, the next output is the sum of a and b.
    check_sum_when_sel_high: assert property (
        @(posedge clk) disable iff (reset)
        sel |=> (out == $past(a + b))
    );

    // With sel low and zero operands, the next output is zero.
    check_zero_product_when_operands_zero: assert property (
        @(posedge clk) disable iff (reset)
        (!sel && (a == 8'sd0) && (b == 8'sd0)) |=> (out == 16'sd0)
    );

    // With sel high and zero operands, the next output is zero.
    check_zero_sum_when_operands_zero: assert property (
        @(posedge clk) disable iff (reset)
        (sel && (a == 8'sd0) && (b == 8'sd0)) |=> (out == 16'sd0)
    );

    // With sel low and equal operands, the next output is the square of a.
    check_square_when_operands_equal: assert property (
        @(posedge clk) disable iff (reset)
        (!sel && (a == b)) |=> (out == $past(a * a))
    );

    // With sel high and equal operands, the next output is twice a.
    check_double_when_operands_equal: assert property (
        @(posedge clk) disable iff (reset)
        (sel && (a == b)) |=> (out == ($past(a) + $past(a)))
    );

endmodule