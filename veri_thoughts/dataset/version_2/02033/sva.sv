module signed_multiplier_sva (
    input logic clk,
    input signed [3:0] A,
    input signed [3:0] B,
    input signed [7:0] P
);
    // P must always equal A * B.
    check_product_definition: assert property (
        @(posedge clk) P == (A * B)
    );

    // Commutativity holds: P equals B * A.
    check_commutativity: assert property (
        @(posedge clk) P == (B * A)
    );

    // If A is zero, P must be zero.
    check_zero_with_A: assert property (
        @(posedge clk) (A == 4'sd0) |-> (P == 8'sd0)
    );

    // If B is zero, P must be zero.
    check_zero_with_B: assert property (
        @(posedge clk) (B == 4'sd0) |-> (P == 8'sd0)
    );

    // If A is +1, P must equal B.
    check_identity_A_one: assert property (
        @(posedge clk) (A == 4'sd1) |-> (P == $signed(B))
    );

    // If B is +1, P must equal A.
    check_identity_B_one: assert property (
        @(posedge clk) (B == 4'sd1) |-> (P == $signed(A))
    );

    // If A is -1, P must equal negated B (properly sign-extended).
    check_negone_A: assert property (
        @(posedge clk) (A == -4'sd1) |-> (P == -$signed({{4{B[3]}}, B}))
    );

    // If B is -1, P must equal negated A (properly sign-extended).
    check_negone_B: assert property (
        @(posedge clk) (B == -4'sd1) |-> (P == -$signed({{4{A[3]}}, A}))
    );

    // For non-zero operands, product sign equals XOR of operand signs.
    check_sign_rule_nonzero: assert property (
        @(posedge clk) (A != 4'sd0 && B != 4'sd0) |-> (P[7] == (A[3] ^ B[3]))
    );

    // LSB of product equals AND of operand LSBs.
    check_lsb_rule: assert property (
        @(posedge clk) P[0] == (A[0] & B[0])
    );
endmodule