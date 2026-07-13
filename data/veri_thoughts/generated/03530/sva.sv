module add_sub_overflow_sva (
    input logic       clk,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic       Cn,
    input logic [3:0] S,
    input logic       V
);

    // External sampling clock; RTL has no clock or reset.

    // In add mode, S is the 4-bit sum of A and B.
    check_add_result: assert property (
        @(posedge clk) (Cn == 1'b0) |-> (S == (A + B))
    );

    // In subtract mode, S is the 4-bit difference A minus B.
    check_sub_result: assert property (
        @(posedge clk) (Cn == 1'b1) |-> (S == (A - B))
    );

    // In add mode, V matches the implemented overflow equation.
    check_add_overflow_exact: assert property (
        @(posedge clk) (Cn == 1'b0) |-> (V == ((A[3] & B[3] & ~S[3]) | (~A[3] & ~B[3] & S[3])))
    );

    // In subtract mode, V matches the implemented overflow equation.
    check_sub_overflow_exact: assert property (
        @(posedge clk) (Cn == 1'b1) |-> (V == ((A[3] & ~B[3] & ~S[3]) | (~A[3] & B[3] & S[3])))
    );

    // Adding two negative operands with a non-negative result sets overflow.
    check_add_neg_neg_to_pos_overflow: assert property (
        @(posedge clk) ((Cn == 1'b0) && A[3] && B[3] && ~S[3]) |-> (V == 1'b1)
    );

    // Adding two non-negative operands with a negative result sets overflow.
    check_add_pos_pos_to_neg_overflow: assert property (
        @(posedge clk) ((Cn == 1'b0) && ~A[3] && ~B[3] && S[3]) |-> (V == 1'b1)
    );

    // Adding operands with opposite signs cannot overflow.
    check_add_mixed_sign_no_overflow: assert property (
        @(posedge clk) ((Cn == 1'b0) && (A[3] != B[3])) |-> (V == 1'b0)
    );

    // Subtracting a non-negative operand from a negative operand can overflow high.
    check_sub_neg_minus_pos_overflow: assert property (
        @(posedge clk) ((Cn == 1'b1) && A[3] && ~B[3] && ~S[3]) |-> (V == 1'b1)
    );

    // Subtracting a negative operand from a non-negative operand can overflow low.
    check_sub_pos_minus_neg_overflow: assert property (
        @(posedge clk) ((Cn == 1'b1) && ~A[3] && B[3] && S[3]) |-> (V == 1'b1)
    );

    // Subtracting same-sign operands cannot overflow.
    check_sub_same_sign_no_overflow: assert property (
        @(posedge clk) ((Cn == 1'b1) && (A[3] == B[3])) |-> (V == 1'b0)
    );

endmodule