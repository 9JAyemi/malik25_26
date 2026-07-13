module csa_generate_adder_32bit_sva (
    input logic CLK,
    input logic [31:0] A,
    input logic [31:0] B,
    output logic [31:0] S,
    output logic C32
);

    // Combinational logic assertions
    // A and B inputs should not change during the addition process
    comb_A_stable: assert property (
        @(posedge CLK) disable iff (!CLK) $stable(A)
    );
    comb_B_stable: assert property (
        @(posedge CLK) disable iff (!CLK) $stable(B)
    );

    // S and C32 outputs should be stable during the addition process
    comb_S_stable: assert property (
        @(posedge CLK) disable iff (!CLK) $stable(S)
    );
    comb_C32_stable: assert property (
        @(posedge CLK) disable iff (!CLK) $stable(C32)
    );

    // Ripple carry adder should produce correct sum and carry
    // First stage of pipeline
    rca1_sum_correct: assert property (
        @(posedge CLK) disable iff (!CLK) (S[0] == A[0] + B[0] + 1'b0)
    );
    rca1_carry_correct: assert property (
        @(posedge CLK) disable iff (!CLK) (C[0] == (A[0] & B[0]) | (1'b0 & (A[0] | B[0])))
    );

    // Second stage of pipeline
    rca2_sum_correct: assert property (
        @(posedge CLK) disable iff (!CLK) (S2[0] == S1[0] + P[0] + G[31])
    );
    rca2_carry_correct: assert property (
        @(posedge CLK) disable iff (!CLK) (C[31] == (S1[0] & P[0]) | (G[31] & (S1[0] | P[0])))
    );

    // Final stage of pipeline
    final_sum_correct: assert property (
        @(posedge CLK) disable iff (!CLK) (S == S2)
    );
    final_carry_correct: assert property (
        @(posedge CLK) disable iff (!CLK) (C32 == C[31])
    );

endmodule