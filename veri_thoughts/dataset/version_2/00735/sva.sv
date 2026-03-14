module adder4bit_sva (
    input logic CLK,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic C_IN,
    input logic [3:0] SUM,
    input logic C_OUT
);
    // Helper carry expectations derived from ripple structure
    logic c0_exp, c1_exp, c2_exp, c3_exp;
    assign c0_exp = (A[0] & B[0]) | (B[0] & C_IN) | (A[0] & C_IN);
    assign c1_exp = (A[1] & B[1]) | (B[1] & c0_exp) | (A[1] & c0_exp);
    assign c2_exp = (A[2] & B[2]) | (B[2] & c1_exp) | (A[2] & c1_exp);
    assign c3_exp = (A[3] & B[3]) | (B[3] & c2_exp) | (A[3] & c2_exp);

    ///// Arithmetic correctness /////
    // 5-bit result must equal A + B + C_IN.
    check_total_sum_correct: assert property (
        @(posedge CLK) {C_OUT, SUM} == ({1'b0, A} + {1'b0, B} + C_IN)
    );

    ///// Bit-slice sum equations /////
    // LSB sum equals XOR of A[0], B[0], and C_IN.
    check_sum_bit0_is_fulladder_xor: assert property (
        @(posedge CLK) SUM[0] == (A[0] ^ B[0] ^ C_IN)
    );
    // SUM[1] equals XOR of A[1], B[1], and carry from bit0.
    check_sum_bit1_is_fulladder_xor: assert property (
        @(posedge CLK) SUM[1] == (A[1] ^ B[1] ^ c0_exp)
    );
    // SUM[2] equals XOR of A[2], B[2], and carry from bit1.
    check_sum_bit2_is_fulladder_xor: assert property (
        @(posedge CLK) SUM[2] == (A[2] ^ B[2] ^ c1_exp)
    );
    // SUM[3] equals XOR of A[3], B[3], and carry from bit2.
    check_sum_bit3_is_fulladder_xor: assert property (
        @(posedge CLK) SUM[3] == (A[3] ^ B[3] ^ c2_exp)
    );

    ///// Carry-out correctness /////
    // Final carry-out equals carry generated into bit3 stage.
    check_carry_out_ripple_correct: assert property (
        @(posedge CLK) C_OUT == c3_exp
    );

    ///// Basic identities and corner cases /////
    // Adding zero with no carry-in yields zero and no carry-out.
    check_zero_plus_zero_no_carry: assert property (
        @(posedge CLK) (A == 4'b0000) && (B == 4'b0000) && (C_IN == 1'b0) |-> (SUM == 4'b0000) && (C_OUT == 1'b0)
    );
    // Adding B with A=0 and no carry-in yields SUM=B and no carry-out.
    check_identity_add_zero_A: assert property (
        @(posedge CLK) (A == 4'b0000) && (C_IN == 1'b0) |-> (SUM == B) && (C_OUT == 1'b0)
    );
    // Adding A with B=0 and no carry-in yields SUM=A and no carry-out.
    check_identity_add_zero_B: assert property (
        @(posedge CLK) (B == 4'b0000) && (C_IN == 1'b0) |-> (SUM == A) && (C_OUT == 1'b0)
    );
    // 0xF + 0x0 + 1 overflows to SUM=0 and C_OUT=1.
    check_overflow_F_plus_0_plus_1: assert property (
        @(posedge CLK) (A == 4'hF) && (B == 4'h0) && (C_IN == 1'b1) |-> (SUM == 4'h0) && (C_OUT == 1'b1)
    );
endmodule