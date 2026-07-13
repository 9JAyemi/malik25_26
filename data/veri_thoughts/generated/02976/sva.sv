module simple_calculator_sva (
    input logic CLK,
    input logic [7:0] a,
    input logic [7:0] b,
    input logic [7:0] sum,
    input logic [7:0] difference,
    input logic [7:0] product,
    input logic [7:0] quotient
);
    // Combinational DUT; no reset; external CLK used only for SVA sampling.

    ///// Arithmetic correctness /////
    // Sum equals lower 8 bits of a+b.
    check_sum_truncated_add: assert property (
        @(posedge CLK) sum == (a + b)[7:0]
    );

    // Difference equals unsigned absolute difference.
    check_difference_abs: assert property (
        @(posedge CLK) difference == ((a > b) ? (a - b) : (b - a))
    );

    // Product equals lower 8 bits of a*b.
    check_product_truncated_mul: assert property (
        @(posedge CLK) product == (a * b)[7:0]
    );

    // When b != 0, quotient equals a/b.
    check_quotient_when_b_nonzero: assert property (
        @(posedge CLK) (b != 8'd0) |-> (quotient == (a / b))
    );

    ///// Identities and corner cases /////
    // When a == b, difference is zero.
    check_diff_zero_when_equal: assert property (
        @(posedge CLK) (a == b) |-> (difference == 8'd0)
    );

    // When a != b, difference is non-zero.
    check_diff_nonzero_when_neq: assert property (
        @(posedge CLK) (a != b) |-> (difference != 8'd0)
    );

    // If either operand is zero, product is zero.
    check_product_zero_if_operand_zero: assert property (
        @(posedge CLK) ((a == 8'd0) || (b == 8'd0)) |-> (product == 8'd0)
    );

    // If a == 1, product equals b.
    check_product_identity_a_one: assert property (
        @(posedge CLK) (a == 8'd1) |-> (product == b)
    );

    // If b == 1, product equals a.
    check_product_identity_b_one: assert property (
        @(posedge CLK) (b == 8'd1) |-> (product == a)
    );

    // If b == 1, quotient equals a.
    check_quotient_identity_div_by_one: assert property (
        @(posedge CLK) (b == 8'd1) |-> (quotient == a)
    );

    // If a == b and nonzero, quotient equals 1.
    check_quotient_one_when_equal_nonzero: assert property (
        @(posedge CLK) ((a == b) && (b != 8'd0)) |-> (quotient == 8'd1)
    );

    // If a == 0, sum equals b.
    check_sum_identity_a_zero: assert property (
        @(posedge CLK) (a == 8'd0) |-> (sum == b)
    );

    // If b == 0, sum equals a.
    check_sum_identity_b_zero: assert property (
        @(posedge CLK) (b == 8'd0) |-> (sum == a)
    );
endmodule