module adder16_sva (
    input logic        clk,
    input logic [15:0] A,
    input logic [15:0] B,
    input logic [15:0] Y
);

    // Y must always equal the 16-bit sum of A and B.
    check_sum_matches_inputs: assert property (
        @(posedge clk) Y == (A + B)
    );

    // Adding zero on B must pass A through unchanged.
    check_zero_on_b: assert property (
        @(posedge clk) (B == 16'h0000) |-> (Y == A)
    );

    // Adding zero on A must pass B through unchanged.
    check_zero_on_a: assert property (
        @(posedge clk) (A == 16'h0000) |-> (Y == B)
    );

    // Complementary inputs must sum to all ones.
    check_complementary_inputs_all_ones: assert property (
        @(posedge clk) (B == ~A) |-> (Y == 16'hFFFF)
    );

    // Adding one to all ones must wrap around to zero.
    check_max_plus_one_wraps: assert property (
        @(posedge clk) ((A == 16'hFFFF) && (B == 16'h0001)) |-> (Y == 16'h0000)
    );

    // The least-significant sum bit must match A[0] xor B[0].
    check_lsb_sum_bit: assert property (
        @(posedge clk) Y[0] == (A[0] ^ B[0])
    );

endmodule