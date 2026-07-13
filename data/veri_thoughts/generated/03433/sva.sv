module addition_sva (
    input logic clk,
    input logic [7:0] a,
    input logic [7:0] b,
    input logic [7:0] sum,
    input logic overflow
);

    // sum is the low 8 bits of the zero-extended addition.
    check_sum_matches_addition: assert property (
        @(posedge clk) disable iff (1'b0)
        sum == (({1'b0, a} + {1'b0, b})[7:0])
    );

    // overflow matches the RTL overflow expression.
    check_overflow_matches_expression: assert property (
        @(posedge clk) disable iff (1'b0)
        overflow == (((a[7] == b[7]) && (sum[7] != a[7])) ||
                     ((a[7] != b[7]) && (sum[7] == (({1'b0, a} + {1'b0, b})[8]))))
    );

    // Same-sign operands overflow exactly when the sum sign flips.
    check_same_sign_overflow_equivalence: assert property (
        @(posedge clk) disable iff (1'b0)
        (a[7] == b[7]) |-> (overflow == (sum[7] != a[7]))
    );

    // Different-sign operands do not overflow.
    check_different_sign_no_overflow: assert property (
        @(posedge clk) disable iff (1'b0)
        (a[7] != b[7]) |-> (overflow == 1'b0)
    );

    // Two positive operands producing a negative sum must assert overflow.
    check_positive_overflow_case: assert property (
        @(posedge clk) disable iff (1'b0)
        ((a[7] == 1'b0) && (b[7] == 1'b0) && (sum[7] == 1'b1)) |-> (overflow == 1'b1)
    );

    // Two negative operands producing a positive sum must assert overflow.
    check_negative_overflow_case: assert property (
        @(posedge clk) disable iff (1'b0)
        ((a[7] == 1'b1) && (b[7] == 1'b1) && (sum[7] == 1'b0)) |-> (overflow == 1'b1)
    );

    // Adding zero on a passes b through with no overflow.
    check_a_zero_passthrough: assert property (
        @(posedge clk) disable iff (1'b0)
        (a == 8'h00) |-> ((sum == b) && (overflow == 1'b0))
    );

    // Adding zero on b passes a through with no overflow.
    check_b_zero_passthrough: assert property (
        @(posedge clk) disable iff (1'b0)
        (b == 8'h00) |-> ((sum == a) && (overflow == 1'b0))
    );

endmodule