module adder4_sva (
    input logic       clk,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic [3:0] S,
    input logic       Cout
);

    // LSB sum is the XOR of A[0] and B[0].
    check_lsb_sum: assert property (
        @(posedge clk) S[0] == (A[0] ^ B[0])
    );

    // Bit 1 sum includes the carry from bit 0.
    check_bit1_sum: assert property (
        @(posedge clk) S[1] == (A[1] ^ B[1] ^ (A[0] & B[0]))
    );

    // Bit 2 sum includes the ripple carry from bits 1:0.
    check_bit2_sum: assert property (
        @(posedge clk)
        S[2] == (A[2] ^ B[2] ^
                 ((A[1] & B[1]) |
                  (A[1] & (A[0] & B[0])) |
                  (B[1] & (A[0] & B[0]))))
    );

    // The 4-bit sum and carry-out match zero-extended addition.
    check_full_sum: assert property (
        @(posedge clk) {Cout, S} == ({1'b0, A} + {1'b0, B})
    );

    // Zero on A passes B through with no carry-out.
    check_zero_a_passthrough: assert property (
        @(posedge clk) (A == 4'h0) |-> ({Cout, S} == {1'b0, B})
    );

    // Zero on B passes A through with no carry-out.
    check_zero_b_passthrough: assert property (
        @(posedge clk) (B == 4'h0) |-> ({Cout, S} == {1'b0, A})
    );

    // Adding 0xF and 0xF produces 0x1E.
    check_all_ones_addition: assert property (
        @(posedge clk) ((A == 4'hF) && (B == 4'hF)) |-> ({Cout, S} == 5'h1E)
    );

endmodule