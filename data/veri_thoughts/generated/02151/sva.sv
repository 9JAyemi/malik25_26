module ripple_carry_adder_sva (
    input logic CLK,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic Cin,
    input logic [3:0] S,
    input logic Cout
);
    // Local carry expressions derived from the ripple chain
    let c0 = (A[0] & B[0]) | (A[0] & Cin) | (B[0] & Cin);
    let c1 = (A[1] & B[1]) | (A[1] & c0)  | (B[1] & c0);
    let c2 = (A[2] & B[2]) | (A[2] & c1)  | (B[2] & c1);
    let c3 = (A[3] & B[3]) | (A[3] & c2)  | (B[3] & c2);
    let carry_in_vec = {c2, c1, c0, Cin};

    // Overall 5-bit sum equals A + B + Cin.
    adder_sum_correct: assert property (
        @(posedge CLK) {Cout, S} == ({1'b0, A} + {1'b0, B} + Cin)
    );

    // LSB sum is XOR of A[0], B[0], and Cin.
    sum_bit0_xor: assert property (
        @(posedge CLK) S[0] == (A[0] ^ B[0] ^ Cin)
    );

    // Bit1 sum uses c0 as carry in.
    sum_bit1_xor_with_c0: assert property (
        @(posedge CLK) S[1] == (A[1] ^ B[1] ^ c0)
    );

    // Bit2 sum uses c1 as carry in.
    sum_bit2_xor_with_c1: assert property (
        @(posedge CLK) S[2] == (A[2] ^ B[2] ^ c1)
    );

    // Bit3 sum uses c2 as carry in.
    sum_bit3_xor_with_c2: assert property (
        @(posedge CLK) S[3] == (A[3] ^ B[3] ^ c2)
    );

    // Cout equals the final carry c3.
    cout_equals_c3: assert property (
        @(posedge CLK) Cout == c3
    );

    // Vector sum equals A ^ B ^ carry_in for each bit.
    sum_vector_xor_correct: assert property (
        @(posedge CLK) S == (A ^ B ^ carry_in_vec)
    );

    // If B==0 and Cin==0, output equals A and no carry.
    identity_when_B_zero_and_Cin_zero: assert property (
        @(posedge CLK) (B == 4'b0000 && Cin == 1'b0) |-> (S == A && Cout == 1'b0)
    );

    // If A==0 and Cin==0, output equals B and no carry.
    identity_when_A_zero_and_Cin_zero: assert property (
        @(posedge CLK) (A == 4'b0000 && Cin == 1'b0) |-> (S == B && Cout == 1'b0)
    );

    // If A==0 and B==0, S reflects Cin in LSB and Cout==0.
    both_operands_zero_behavior: assert property (
        @(posedge CLK) (A == 4'b0000 && B == 4'b0000) |-> (S == {3'b000, Cin} && Cout == 1'b0)
    );
endmodule