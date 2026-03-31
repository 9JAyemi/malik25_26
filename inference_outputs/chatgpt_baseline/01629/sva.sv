module binary_adder_sva (
    input  logic        CLK,   // External clock for assertions (RTL has no clock/reset)
    input  logic [3:0]  A,
    input  logic [3:0]  B,
    input  logic [3:0]  C
);
    // Summary: No clock/reset in RTL; purely combinational ripple-carry adder (A+B) with 4-bit sum (no carry-out).

    // Helper expressions for ripple-carry chain derived from RTL structure
    let c1 = (A[0] & B[0]);
    let c2 = (A[1] & B[1]) | (A[1] & c1) | (B[1] & c1);
    let c3 = (A[2] & B[2]) | (A[2] & c2) | (B[2] & c2);

    ///// Functional correctness /////
    // C is the 4-bit sum of A and B modulo 16.
    sum_mod16_correct: assert property (
        @(posedge CLK) disable iff (1'b0) C == (A + B)[3:0]
    );

    // LSB is pure XOR since cin=0 at bit 0.
    bit0_pure_xor: assert property (
        @(posedge CLK) disable iff (1'b0) C[0] == (A[0] ^ B[0])
    );

    // Bit1 equals A1 ^ B1 ^ carry from bit0 (A0 & B0).
    bit1_with_carry1: assert property (
        @(posedge CLK) disable iff (1'b0) C[1] == (A[1] ^ B[1] ^ c1)
    );

    // Bit2 equals A2 ^ B2 ^ carry from bit1.
    bit2_with_carry2: assert property (
        @(posedge CLK) disable iff (1'b0) C[2] == (A[2] ^ B[2] ^ c2)
    );

    // Bit3 equals A3 ^ B3 ^ carry from bit2.
    bit3_with_carry3: assert property (
        @(posedge CLK) disable iff (1'b0) C[3] == (A[3] ^ B[3] ^ c3)
    );

    ///// Identities /////
    // Adding zero on B leaves A unchanged.
    identity_when_B_zero: assert property (
        @(posedge CLK) disable iff (1'b0) (B == 4'h0) |-> (C == A)
    );

    // Adding zero on A leaves B unchanged.
    identity_when_A_zero: assert property (
        @(posedge CLK) disable iff (1'b0) (A == 4'h0) |-> (C == B)
    );

    // Zero plus zero yields zero.
    zero_plus_zero_zero: assert property (
        @(posedge CLK) disable iff (1'b0) (A == 4'h0 && B == 4'h0) |-> (C == 4'h0)
    );

    // Adding one on B increments A modulo 16.
    increment_when_B_is_one: assert property (
        @(posedge CLK) disable iff (1'b0) (B == 4'h1) |-> (C == (A + 4'h1)[3:0])
    );

    ///// Carry-free condition /////
    // If no generates anywhere (A & B == 0), sum reduces to bitwise XOR.
    no_generate_no_carry_xor: assert property (
        @(posedge CLK) disable iff (1'b0) ((A & B) == 4'h0) |-> (C == (A ^ B))
    );
endmodule