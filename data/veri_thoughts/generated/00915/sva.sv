module RCA_4_sva (
    input logic CLK,
    input logic RESETn,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic Ci,
    input logic [3:0] S,
    input logic Co,
    input logic [3:1] CTMP
);
    // LSB sum equals XOR of A[0], B[0], and Ci.
    bit0_sum_is_xor: assert property (
        @(posedge CLK) disable iff (!RESETn) S[0] == (A[0] ^ B[0] ^ Ci)
    );

    // Carry from bit0 equals (A0&B0) | (Ci&(A0^B0)).
    bit0_carry1_is_formula: assert property (
        @(posedge CLK) disable iff (!RESETn) CTMP[1] == ((A[0] & B[0]) | (Ci & (A[0] ^ B[0])))
    );

    // Bit1 sum equals XOR of A[1], B[1], and CTMP[1].
    bit1_sum_is_xor: assert property (
        @(posedge CLK) disable iff (!RESETn) S[1] == (A[1] ^ B[1] ^ CTMP[1])
    );

    // Carry from bit1 equals (A1&B1) | (CTMP1&(A1^B1)).
    bit1_carry2_is_formula: assert property (
        @(posedge CLK) disable iff (!RESETn) CTMP[2] == ((A[1] & B[1]) | (CTMP[1] & (A[1] ^ B[1])))
    );

    // Bit2 sum equals XOR of A[2], B[2], and CTMP[2].
    bit2_sum_is_xor: assert property (
        @(posedge CLK) disable iff (!RESETn) S[2] == (A[2] ^ B[2] ^ CTMP[2])
    );

    // Carry from bit2 equals (A2&B2) | (CTMP2&(A2^B2)).
    bit2_carry3_is_formula: assert property (
        @(posedge CLK) disable iff (!RESETn) CTMP[3] == ((A[2] & B[2]) | (CTMP[2] & (A[2] ^ B[2])))
    );

    // Bit3 sum equals XOR of A[3], B[3], and CTMP[3].
    bit3_sum_is_xor: assert property (
        @(posedge CLK) disable iff (!RESETn) S[3] == (A[3] ^ B[3] ^ CTMP[3])
    );

    // Final carry equals (A3&B3) | (CTMP3&(A3^B3)).
    final_carry_is_formula: assert property (
        @(posedge CLK) disable iff (!RESETn) Co == ((A[3] & B[3]) | (CTMP[3] & (A[3] ^ B[3])))
    );

    // Overall 5-bit result {Co,S} equals A + B + Ci.
    overall_addition_correct: assert property (
        @(posedge CLK) disable iff (!RESETn) {Co, S} == ({1'b0, A} + {1'b0, B} + {4'b0, Ci})
    );

    // If inputs are stable across cycles, outputs are stable as well.
    outputs_stable_when_inputs_stable: assert property (
        @(posedge CLK) disable iff (!RESETn) ($stable(A) && $stable(B) && $stable(Ci)) |-> $stable({S, Co})
    );
endmodule