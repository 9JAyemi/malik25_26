module binary_subtractor_32bit_sva (
    input logic        clk,
    input logic [31:0] A,
    input logic [31:0] B,
    input logic [31:0] S
);

// S equals A minus B (32-bit two's complement).
    check_subtraction_result: assert property (
        @(posedge clk) S == (A - B)
    );

// LSB of S equals XOR of LSBs of A and B.
    check_lsb_xor: assert property (
        @(posedge clk) S[0] == (A[0] ^ B[0])
    );

// When B is zero, S equals A.
    check_zero_subtrahend: assert property (
        @(posedge clk) (B == 32'h0) |-> (S == A)
    );

// When A is zero, S equals two's complement of B.
    check_zero_minuend: assert property (
        @(posedge clk) (A == 32'h0) |-> (S == ~B + 32'h1)
    );

// When A equals B, S is zero.
    check_equal_operands: assert property (
        @(posedge clk) (A == B) |-> (S == 32'h0)
    );

// Subtracting the minimum 32-bit value wraps to the maximum value.
    check_wrap_from_min: assert property (
        @(posedge clk) (B == 32'h8000_0000) |-> (S == 32'h7FFF_FFFF)
    );

// Subtracting the maximum 32-bit value wraps to one.
    check_wrap_from_max: assert property (
        @(posedge clk) (B == 32'h7FFF_FFFF) |-> (S == 32'h0000_0001)
    );

endmodule
