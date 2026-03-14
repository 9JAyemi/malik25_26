module mult_16bit_signed_sva (
    input logic CLK,
    input signed [15:0] M,
    input signed [15:0] N,
    input signed [31:0] P
);
    // P equals the signed product of M and N.
    check_product_correct: assert property (
        @(posedge CLK) disable iff ($initstate) P == M * N
    );

    // If M is zero then P is zero.
    check_zero_multiplicand_M: assert property (
        @(posedge CLK) disable iff ($initstate) (M == 16'sd0) |-> (P == 32'sd0)
    );

    // If N is zero then P is zero.
    check_zero_multiplicand_N: assert property (
        @(posedge CLK) disable iff ($initstate) (N == 16'sd0) |-> (P == 32'sd0)
    );

    // If M is one then P equals N.
    check_one_multiplicand_M: assert property (
        @(posedge CLK) disable iff ($initstate) (M == 16'sd1) |-> (P == N)
    );

    // If N is one then P equals M.
    check_one_multiplicand_N: assert property (
        @(posedge CLK) disable iff ($initstate) (N == 16'sd1) |-> (P == M)
    );

    // If M is minus one then P equals -N.
    check_neg_one_multiplicand_M: assert property (
        @(posedge CLK) disable iff ($initstate) (M == -16'sd1) |-> (P == -N)
    );

    // If N is minus one then P equals -M.
    check_neg_one_multiplicand_N: assert property (
        @(posedge CLK) disable iff ($initstate) (N == -16'sd1) |-> (P == -M)
    );

    // For non-zero operands, product sign equals XOR of operand signs.
    check_product_sign: assert property (
        @(posedge CLK) disable iff ($initstate) ((M != 16'sd0) && (N != 16'sd0)) |-> (P[31] == (M[15] ^ N[15]))
    );

    // Zero product implies at least one operand is zero.
    check_zero_product_implication: assert property (
        @(posedge CLK) disable iff ($initstate) (P == 32'sd0) |-> ((M == 16'sd0) || (N == 16'sd0))
    );

    // If inputs are stable cycle-to-cycle, output remains stable.
    check_stability_when_inputs_stable: assert property (
        @(posedge CLK) disable iff ($initstate) (M == $past(M) && N == $past(N)) |-> (P == $past(P))
    );
endmodule