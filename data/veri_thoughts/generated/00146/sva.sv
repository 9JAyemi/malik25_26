module adder_sva (
    input logic       clk,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic [3:0] S,
    input logic       C
);

    // Full output equals the 5-bit sum of the inputs.
    check_full_sum: assert property (
        @(posedge clk) {C, S} == ({1'b0, A} + {1'b0, B})
    );

    // Low sum bits match the low nibble of the addition result.
    check_sum_low_bits: assert property (
        @(posedge clk) {1'b0, S} == (({1'b0, A} + {1'b0, B}) & 5'h0F)
    );

    // Carry is high exactly when the sum reaches 16 or more.
    check_carry_matches_overflow: assert property (
        @(posedge clk) C == (({1'b0, A} + {1'b0, B}) >= 5'd16)
    );

    // The least significant sum bit is the XOR of input LSBs.
    check_lsb_xor: assert property (
        @(posedge clk) S[0] == (A[0] ^ B[0])
    );

    // Adding zero on A passes B through with no carry.
    check_zero_a_passthrough: assert property (
        @(posedge clk) (A == 4'd0) |-> ({C, S} == {1'b0, B})
    );

    // Adding zero on B passes A through with no carry.
    check_zero_b_passthrough: assert property (
        @(posedge clk) (B == 4'd0) |-> ({C, S} == {1'b0, A})
    );

    // The maximum input pair produces decimal 30.
    check_max_plus_max: assert property (
        @(posedge clk) ((A == 4'hF) && (B == 4'hF)) |-> ({C, S} == 5'h1E)
    );

    // Fifteen plus one produces the carry boundary value 16.
    check_carry_boundary: assert property (
        @(posedge clk) (((A == 4'hF) && (B == 4'h1)) || ((A == 4'h1) && (B == 4'hF))) |-> ({C, S} == 5'h10)
    );

endmodule