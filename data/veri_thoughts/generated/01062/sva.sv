module ripple_adder_sva (
    input logic clk,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic CIN,
    input logic [3:0] S,
    input logic COUT
);
    // Local expected results based on the RTL's combinational logic
    logic p0, p1, p2, p3;
    logic c0, c1, c2, c3;
    logic [4:0] exp_sum5;

    assign p0 = A[0] ^ B[0];
    assign p1 = A[1] ^ B[1];
    assign p2 = A[2] ^ B[2];
    assign p3 = A[3] ^ B[3];

    assign c0 = (A[0] & B[0]) | (p0 & CIN);
    assign c1 = (A[1] & B[1]) | (p1 & c0);
    assign c2 = (A[2] & B[2]) | (p2 & c1);
    assign c3 = (A[3] & B[3]) | (p3 & c2);

    assign exp_sum5 = {1'b0, A} + {1'b0, B} + CIN;

    // Overall 5-bit sum equals A + B + CIN.
    overall_addition_correct: assert property (
        @(posedge clk) {COUT, S} == exp_sum5
    );

    // LSB sum is XOR of A[0], B[0], and CIN.
    sum_bit0_parity: assert property (
        @(posedge clk) S[0] == (A[0] ^ B[0] ^ CIN)
    );

    // Bit1 sum is XOR of A[1], B[1], and carry0.
    sum_bit1_parity_with_carry0: assert property (
        @(posedge clk) S[1] == (p1 ^ c0)
    );

    // Bit2 sum is XOR of A[2], B[2], and carry1.
    sum_bit2_parity_with_carry1: assert property (
        @(posedge clk) S[2] == (p2 ^ c1)
    );

    // Bit3 sum is XOR of A[3], B[3], and carry2.
    sum_bit3_parity_with_carry2: assert property (
        @(posedge clk) S[3] == (p3 ^ c2)
    );

    // Final carry-out equals carry3 from the ripple chain.
    cout_matches_carry3: assert property (
        @(posedge clk) COUT == c3
    );

    // With CIN=0, the result equals A + B.
    cin_zero_behavior: assert property (
        @(posedge clk) (CIN == 1'b0) |-> ({COUT, S} == ({1'b0, A} + {1'b0, B}))
    );

    // With A=0 and B=0, sum is CIN in bit0 and no carry out.
    zero_inputs_behavior: assert property (
        @(posedge clk) (A == 4'b0000 && B == 4'b0000) |-> ({COUT, S} == {1'b0, 3'b000, CIN})
    );

    // With B=0 and CIN=0, sum passes A and no carry out.
    passthrough_A_when_B_zero_no_cin: assert property (
        @(posedge clk) (B == 4'b0000 && CIN == 1'b0) |-> ({COUT, S} == {1'b0, A})
    );

    // With A=0 and CIN=0, sum passes B and no carry out.
    passthrough_B_when_A_zero_no_cin: assert property (
        @(posedge clk) (A == 4'b0000 && CIN == 1'b0) |-> ({COUT, S} == {1'b0, B})
    );

    // If inputs are stable between cycles, outputs remain stable.
    stable_inputs_imply_stable_outputs: assert property (
        @(posedge clk) ($stable(A) && $stable(B) && $stable(CIN)) |-> ($stable(S) && $stable(COUT))
    );
endmodule