module ripple_carry_adder_sva (
    input  logic [3:0] A,
    input  logic [3:0] B,
    input  logic       C_in,
    input  logic       CLK,
    input  logic [3:0] S,
    input  logic       C_out
);
    // Clock: CLK (posedge). No reset. Purely combinational 4-bit ripple-carry adder: {C_out,S} = A + B + C_in.

    // Local combinational expressions for carry chain and sums.
    let c0 = (A[0] & B[0]) | (A[0] & C_in) | (B[0] & C_in);
    let c1 = (A[1] & B[1]) | (A[1] & c0)   | (B[1] & c0);
    let c2 = (A[2] & B[2]) | (A[2] & c1)   | (B[2] & c1);
    let c3 = (A[3] & B[3]) | (A[3] & c2)   | (B[3] & c2);
    let s0 = A[0] ^ B[0] ^ C_in;
    let s1 = A[1] ^ B[1] ^ c0;
    let s2 = A[2] ^ B[2] ^ c1;
    let s3 = A[3] ^ B[3] ^ c2;

    // Output vector equals 5-bit addition of inputs.
    check_add_result_matches_addition: assert property (
        @(posedge CLK) {C_out, S} == ({1'b0, A} + {1'b0, B} + C_in)
    );

    // LSB sum is XOR of A[0], B[0], and C_in.
    check_sum_bit0_xor: assert property (
        @(posedge CLK) S[0] == s0
    );

    // Bit1 sum equals XOR of A[1], B[1], and carry0.
    check_sum_bit1_xor_with_carry0: assert property (
        @(posedge CLK) S[1] == s1
    );

    // Bit2 sum equals XOR of A[2], B[2], and carry1.
    check_sum_bit2_xor_with_carry1: assert property (
        @(posedge CLK) S[2] == s2
    );

    // Bit3 sum equals XOR of A[3], B[3], and carry2.
    check_sum_bit3_xor_with_carry2: assert property (
        @(posedge CLK) S[3] == s3
    );

    // Final carry-out equals majority function of A[3], B[3], and carry2.
    check_carry_out_function: assert property (
        @(posedge CLK) C_out == c3
    );

    // If inputs are unchanged, outputs must be unchanged.
    check_outputs_stable_when_inputs_stable: assert property (
        @(posedge CLK) ($stable(A) && $stable(B) && $stable(C_in)) |-> ($stable(S) && $stable(C_out))
    );

    // Swapping A and B between cycles leaves outputs unchanged.
    check_commutativity_over_two_cycles: assert property (
        @(posedge CLK) ((A == $past(B)) && (B == $past(A)) && (C_in == $past(C_in))) |-> ({C_out, S} == $past({C_out, S}))
    );

    // With A=B=0, S equals C_in on bit0 and carry-out is 0.
    check_zero_operands_behavior: assert property (
        @(posedge CLK) ((A == 4'd0) && (B == 4'd0)) |-> ((S == {3'b000, C_in}) && (C_out == 1'b0))
    );

    // With A=B=15, result equals 30 + C_in.
    check_max_operands_behavior: assert property (
        @(posedge CLK) ((A == 4'hF) && (B == 4'hF)) |-> ({C_out, S} == (5'd30 + C_in))
    );
endmodule