module adder4bit_sva (
    input logic [3:0] A,
    input logic [3:0] B,
    input logic       Ci,
    input logic [3:0] S,
    input logic       Co
);
    // No explicit clock or reset in RTL; pure combinational. Sample assertions on posedge of Ci.

    // Outputs form the 5-bit sum of inputs.
    check_fullsum_correct: assert property (
        @(posedge Ci) {Co, S} == ({1'b0, A} + {1'b0, B} + Ci)
    );

    // LSB sum bit is XOR of A[0], B[0], and Ci.
    check_s0_is_xor: assert property (
        @(posedge Ci) S[0] == (A[0] ^ B[0] ^ Ci)
    );

    // Bit1 sum uses carry from bit0 ripple logic.
    check_s1_is_xor_with_carry0: assert property (
        @(posedge Ci)
            S[1] == (A[1] ^ B[1] ^ ( (A[0] & B[0]) | ((A[0] ^ B[0]) & Ci) ))
    );

    // Bit2 sum uses carry from bit1 ripple logic.
    check_s2_is_xor_with_carry1: assert property (
        @(posedge Ci)
            S[2] == (A[2] ^ B[2] ^
                     ( (A[1] & B[1]) |
                       ((A[1] ^ B[1]) &
                         ( (A[0] & B[0]) | ((A[0] ^ B[0]) & Ci) ))))
    );

    // Bit3 sum uses carry from bit2 ripple logic.
    check_s3_is_xor_with_carry2: assert property (
        @(posedge Ci)
            S[3] == (A[3] ^ B[3] ^
                     ( (A[2] & B[2]) |
                       ((A[2] ^ B[2]) &
                         ( (A[1] & B[1]) |
                           ((A[1] ^ B[1]) &
                             ( (A[0] & B[0]) | ((A[0] ^ B[0]) & Ci) ))))))
    );

    // Carry-out equals ripple-carry from bit3.
    check_co_is_ripple_carry_out: assert property (
        @(posedge Ci)
            Co == ( (A[3] & B[3]) |
                    ((A[3] ^ B[3]) &
                      ( (A[2] & B[2]) |
                        ((A[2] ^ B[2]) &
                          ( (A[1] & B[1]) |
                            ((A[1] ^ B[1]) &
                              ( (A[0] & B[0]) | ((A[0] ^ B[0]) & Ci) )))))))
    );

    // Adding zero (B=0, Ci=0) returns A with no carry.
    check_identity_when_B_zero_and_Ci_zero: assert property (
        @(posedge Ci) (B == 4'b0000 && Ci == 1'b0) |-> (S == A) && (Co == 1'b0)
    );

    // Adding zero (A=0, Ci=0) returns B with no carry.
    check_identity_when_A_zero_and_Ci_zero: assert property (
        @(posedge Ci) (A == 4'b0000 && Ci == 1'b0) |-> (S == B) && (Co == 1'b0)
    );

    // When A=0 and B=0, sum equals Ci in LSB and no carry.
    check_zero_zero_inputs_propagate_ci: assert property (
        @(posedge Ci) (A == 4'b0000 && B == 4'b0000) |-> (S == {3'b000, Ci}) && (Co == 1'b0)
    );

    // Max operands with Ci=1 produce all ones with carry-out.
    check_max_sum_all_ones_with_carry: assert property (
        @(posedge Ci) (A == 4'hF && B == 4'hF && Ci == 1'b1) |-> ({Co, S} == 5'h1F)
    );
endmodule