module four_bit_adder_sva (
    input logic clk,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic [3:0] sum
);

    // Sum must equal the 4-bit addition of A and B.
    check_sum_matches_addition: assert property (
        @(posedge clk) sum == (A + B)
    );

    // Bit 0 sum must match the full-adder XOR equation.
    check_lsb_sum_equation: assert property (
        @(posedge clk) sum[0] == (A[0] ^ B[0] ^ 1'b0)
    );

    // Bit 1 sum must use the carry from bit 0.
    check_bit1_sum_equation: assert property (
        @(posedge clk) sum[1] == (A[1] ^ B[1] ^ (A[0] & B[0]))
    );

    // Bit 2 sum must use the carry from bit 1.
    check_bit2_sum_equation: assert property (
        @(posedge clk) sum[2] == (A[2] ^ B[2] ^ ((A[1] & B[1]) | ((A[1] ^ B[1]) & (A[0] & B[0]))))
    );

    // Bit 3 sum must use the carry from bit 2.
    check_bit3_sum_equation: assert property (
        @(posedge clk) sum[3] == (A[3] ^ B[3] ^ ((A[2] & B[2]) | ((A[2] ^ B[2]) & ((A[1] & B[1]) | ((A[1] ^ B[1]) & (A[0] & B[0]))))))
    );

    // All-zero inputs must produce all-zero outputs.
    check_zero_inputs_zero_output: assert property (
        @(posedge clk) (A == 4'h0 && B == 4'h0) |-> (sum == 4'h0)
    );

    // Adding zero on B must pass A through to the output.
    check_b_zero_passthrough: assert property (
        @(posedge clk) (B == 4'h0) |-> (sum == A)
    );

    // Adding zero on A must pass B through to the output.
    check_a_zero_passthrough: assert property (
        @(posedge clk) (A == 4'h0) |-> (sum == B)
    );

    // Complementary inputs must sum to all ones.
    check_complementary_inputs_all_ones: assert property (
        @(posedge clk) (A == ~B) |-> (sum == 4'hF)
    );

endmodule