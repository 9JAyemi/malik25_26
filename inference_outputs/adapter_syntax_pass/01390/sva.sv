module csa_generate_adder_32bit_sva (
    input logic CLK,
    input logic [31:0] A,
    input logic [31:0] B,
    input logic [31:0] S,
    input logic C32
);
    // No reset in RTL; assertions are sampled on CLK.

    // S equals A + B (32-bit addition).
    check_sum_equals_add: assert property (
        @(posedge CLK) S == (A + B)
    );

    // C32 equals carry-out of A + B (32-bit addition).
    check_carry32_equals_add: assert property (
        @(posedge CLK) C32 == (({1'b0, A} + {1'b0, B}) >= 33'd4294967296)
    );

    // LSB of S equals XOR of LSBs of A and B.
    check_lsb_xor: assert property (
        @(posedge CLK) S[0] == (A[0] ^ B[0])
    );

    // If A is zero, S equals B and C32 is zero.
    check_zero_a_passthrough: assert property (
        @(posedge CLK) (A == 32'h0) |-> ((S == B) && (C32 == 1'b0))
    );

    // If B is zero, S equals A and C32 is zero.
    check_zero_b_passthrough: assert property (
        @(posedge CLK) (B == 32'h0) |-> ((S == A) && (C32 == 1'b0))
    );

    // If A and B are equal, S equals A << 1 and C32 is zero.
    check_equal_inputs_shift: assert property (
        @(posedge CLK) (A == B) |-> ((S == (A << 1)) && (C32 == 1'b0))
    );

    // If A is all ones, S equals ~B and C32 is one.
    check_all_ones_a: assert property (
        @(posedge CLK) (A == 32'hFFFF_FFFF) |-> ((S == ~B) && (C32 == 1'b1))
    );

    // If B is all ones, S equals ~A and C32 is one.
    check_all_ones_b: assert property (
        @(posedge CLK) (B == 32'hFFFF_FFFF) |-> ((S == ~A) && (C32 == 1'b1))
    );

    // If A is all zeros, S equals B and C32 is zero.
    check_all_zeros_a: assert property (
        @(posedge CLK) (A == 32'h0) |-> ((S == B) && (C32 == 1'b0))
    );

    // If B is all zeros, S equals A and C32 is zero.
    check_all_zeros_b: assert property (
        @(posedge CLK) (B == 32'h0) |-> ((S == A) && (C32 == 1'b0))
    );

    // If A is all ones and B is all zeros, S equals all ones and C32 is zero.
    check_all_ones_a_all_zeros_b: assert property (
        @(posedge CLK) ((A == 32'hFFFF_FFFF) && (B == 32'h0)) |-> ((S == 32'hFFFF_FFFF) && (C32 == 1'b0))
    );

    // If A is all zeros and B is all ones, S equals all ones and C32 is zero.
    check_all_zeros_a_all_ones_b: assert property (
        @(posedge CLK) ((A == 32'h0) && (B == 32'hFFFF_FFFF)) |-> ((S == 32'hFFFF_FFFF) && (C32 == 1'b0))
    );

    // If A is all ones and B is all ones, S equals all zeros and C32 is one.
    check_all_ones_a_all_ones_b: assert property (
        @(posedge CLK) ((A == 32'hFFFF_FFFF) && (B == 32'hFFFF_FFFF)) |-> ((S == 32'h0) && (C32 == 1'b1))
    );

endmodule