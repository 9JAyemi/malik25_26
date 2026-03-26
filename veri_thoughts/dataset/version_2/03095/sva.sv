module UAdder_sva (
    input logic        clk,
    input logic [31:0] out,
    input logic        carry_out,
    input logic        overflow,
    input logic [31:0] A,
    input logic [31:0] B,
    input logic        C_in
);

    // Low nibble matches the first 4-bit CLA result.
    check_nibble0_sum: assert property (
        @(posedge clk) out[3:0] == (A[3:0] + B[3:0] + C_in)
    );

    // Second nibble matches a 4-bit add with carry from bits [3:0].
    check_nibble1_sum: assert property (
        @(posedge clk)
        out[7:4] == (A[7:4] + B[7:4] + (({1'b0, A[3:0]} + {1'b0, B[3:0]} + C_in) > 5'h0F))
    );

    // Nibble [15:12] matches a 4-bit add with carry from bits [11:0].
    check_nibble3_sum: assert property (
        @(posedge clk)
        out[15:12] == (A[15:12] + B[15:12] + (({1'b0, A[11:0]} + {1'b0, B[11:0]} + C_in) > 13'h0FFF))
    );

    // Nibble [23:20] matches a 4-bit add with carry from bits [19:0].
    check_nibble5_sum: assert property (
        @(posedge clk)
        out[23:20] == (A[23:20] + B[23:20] + (({1'b0, A[19:0]} + {1'b0, B[19:0]} + C_in) > 21'h0FFFFF))
    );

    // Top nibble matches the final 4-bit CLA result with propagated carry.
    check_nibble7_sum: assert property (
        @(posedge clk)
        out[31:28] == (A[31:28] + B[31:28] + (({1'b0, A[27:0]} + {1'b0, B[27:0]} + C_in) > 29'h0FFFFFFF))
    );

    // Combined carry_out and out equal the full 33-bit sum.
    check_full_sum: assert property (
        @(posedge clk) {carry_out, out} == ({1'b0, A} + {1'b0, B} + C_in)
    );

    // Overflow matches the signed-add overflow condition.
    check_overflow_equation: assert property (
        @(posedge clk)
        overflow == ((A[31] & B[31] & ~out[31]) | (~A[31] & ~B[31] & out[31]))
    );

    // Opposite-sign operands cannot produce signed overflow.
    check_opposite_sign_no_overflow: assert property (
        @(posedge clk) (A[31] ^ B[31]) |-> !overflow
    );

    // Adding zero on B with no carry-in passes A through unchanged.
    check_zero_b_passthrough: assert property (
        @(posedge clk)
        ((B == 32'h0000_0000) && !C_in) |-> ((out == A) && !carry_out && !overflow)
    );

    // Adding zero on A with no carry-in passes B through unchanged.
    check_zero_a_passthrough: assert property (
        @(posedge clk)
        ((A == 32'h0000_0000) && !C_in) |-> ((out == B) && !carry_out && !overflow)
    );

endmodule