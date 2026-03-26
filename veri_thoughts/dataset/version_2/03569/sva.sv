module calculator_sva (
    input logic        clk,
    input logic [3:0]  a,
    input logic [3:0]  b,
    input logic [1:0]  op,
    input logic [3:0]  add_out,
    input logic [3:0]  sub_out,
    input logic [3:0]  mul_out,
    input logic [3:0]  div_out
);

    // add_out always equals the 4-bit sum of a and b.
    check_add_matches_sum: assert property (
        @(posedge clk) add_out == (a + b)
    );

    // sub_out always equals the 4-bit difference of a and b.
    check_sub_matches_difference: assert property (
        @(posedge clk) sub_out == (a - b)
    );

    // mul_out is the upper nibble of the 8-bit product of a and b.
    check_mul_matches_upper_product_nibble: assert property (
        @(posedge clk) mul_out == ((a * b) >> 4)
    );

    // div_out is zero whenever b is zero.
    check_div_zero_returns_zero: assert property (
        @(posedge clk) (b == 4'h0) |-> (div_out == 4'h0)
    );

    // div_out equals a divided by b whenever b is nonzero.
    check_div_nonzero_matches_quotient: assert property (
        @(posedge clk) (b != 4'h0) |-> (div_out == (a / b))
    );

    // Outputs remain stable when a and b remain stable.
    check_outputs_stable_when_operands_stable: assert property (
        @(posedge clk) (!$initstate && $stable(a) && $stable(b)) |-> $stable({add_out, sub_out, mul_out, div_out})
    );

    // Changing op alone does not affect any output.
    check_op_change_has_no_effect: assert property (
        @(posedge clk) (!$initstate && $stable(a) && $stable(b) && !$stable(op)) |-> $stable({add_out, sub_out, mul_out, div_out})
    );

endmodule