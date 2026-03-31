module four_bit_adder_sva (
    input logic CLK,
    input logic RESETn,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic Cin,
    input logic [3:0] S,
    input logic C_out
);
    // Expected carries from ripple chain based on inputs
    logic c0_exp, c1_exp, c2_exp;
    assign c0_exp = (A[0] & B[0]) | (B[0] & Cin) | (A[0] & Cin);
    assign c1_exp = (A[1] & B[1]) | (B[1] & c0_exp) | (A[1] & c0_exp);
    assign c2_exp = (A[2] & B[2]) | (B[2] & c1_exp) | (A[2] & c1_exp);

    // Expected 5-bit arithmetic sum
    logic [4:0] sum5_exp;
    assign sum5_exp = {1'b0, A} + {1'b0, B} + Cin;

    // Combined 5-bit result equals arithmetic sum of operands.
    check_combined_sum: assert property (
        @(posedge CLK) disable iff (!RESETn) {C_out, S} == sum5_exp
    );

    // Sum bit0 is XOR of A0, B0, Cin.
    check_sum_bit0_xor: assert property (
        @(posedge CLK) disable iff (!RESETn) S[0] == (A[0] ^ B[0] ^ Cin)
    );

    // Sum bit1 is XOR of A1, B1, and generated carry from bit0.
    check_sum_bit1_xor: assert property (
        @(posedge CLK) disable iff (!RESETn) S[1] == (A[1] ^ B[1] ^ c0_exp)
    );

    // Sum bit2 is XOR of A2, B2, and generated carry from bit1.
    check_sum_bit2_xor: assert property (
        @(posedge CLK) disable iff (!RESETn) S[2] == (A[2] ^ B[2] ^ c1_exp)
    );

    // Sum bit3 is XOR of A3, B3, and generated carry from bit2.
    check_sum_bit3_xor: assert property (
        @(posedge CLK) disable iff (!RESETn) S[3] == (A[3] ^ B[3] ^ c2_exp)
    );

    // Carry-out is majority of A3, B3, and carry from bit2.
    check_carry_out_majority: assert property (
        @(posedge CLK) disable iff (!RESETn) C_out == ((A[3] & B[3]) | (B[3] & c2_exp) | (A[3] & c2_exp))
    );

    // Lower 4 sum bits equal arithmetic sum lower bits.
    check_sum_lower_bits: assert property (
        @(posedge CLK) disable iff (!RESETn) S == sum5_exp[3:0]
    );

    // Carry-out equals MSB of 5-bit arithmetic sum.
    check_carry_equals_sum_msb: assert property (
        @(posedge CLK) disable iff (!RESETn) C_out == sum5_exp[4]
    );

    // Adding zero and zero with no carry-in yields zero with no carry-out.
    check_zero_plus_zero: assert property (
        @(posedge CLK) disable iff (!RESETn) ((A == 4'b0000) && (B == 4'b0000) && (Cin == 1'b0)) |-> ((S == 4'b0000) && (C_out == 1'b0))
    );

    // Adding zero B with no carry-in returns A and no carry-out.
    check_add_zero_identity_B: assert property (
        @(posedge CLK) disable iff (!RESETn) ((B == 4'b0000) && (Cin == 1'b0)) |-> ((S == A) && (C_out == 1'b0))
    );

    // Adding zero A with no carry-in returns B and no carry-out.
    check_add_zero_identity_A: assert property (
        @(posedge CLK) disable iff (!RESETn) ((A == 4'b0000) && (Cin == 1'b0)) |-> ((S == B) && (C_out == 1'b0))
    );
endmodule