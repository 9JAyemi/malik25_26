module add4_sva (
    input logic clk,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic [4:0] C
);

    // C must equal the 5-bit sum of A and B.
    check_full_add_result: assert property (
        @(posedge clk) C == ({1'b0, A} + {1'b0, B})
    );

    // C[3:0] must match the low 4 bits of the addition.
    check_lower_sum_bits: assert property (
        @(posedge clk) C[3:0] == (A + B)
    );

    // C[4] must reflect carry-out from the 4-bit addition.
    check_carry_out_bit: assert property (
        @(posedge clk) C[4] == (({1'b0, A} + {1'b0, B}) >= 5'd16)
    );

    // The least-significant sum bit must be A[0] XOR B[0].
    check_bit0_xor: assert property (
        @(posedge clk) C[0] == (A[0] ^ B[0])
    );

    // Bit 1 must include the carry from bit 0.
    check_bit1_with_carry0: assert property (
        @(posedge clk) C[1] == (A[1] ^ B[1] ^ (A[0] & B[0]))
    );

    // Adding zero on A must pass B through.
    check_zero_a_identity: assert property (
        @(posedge clk) (A == 4'h0) |-> (C == {1'b0, B})
    );

    // Adding zero on B must pass A through.
    check_zero_b_identity: assert property (
        @(posedge clk) (B == 4'h0) |-> (C == {1'b0, A})
    );

endmodule