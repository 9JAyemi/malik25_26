module adder_16bit_sva (
    input logic        clk,
    input logic [15:0] A,
    input logic [15:0] B,
    input logic [15:0] S,
    input logic        C
);

    // Full output must match the 17-bit sum of A and B.
    check_full_sum: assert property (
        @(posedge clk) {C, S} == ({1'b0, A} + {1'b0, B})
    );

    // S must be the low 16 bits of the addition result.
    check_sum_low_bits: assert property (
        @(posedge clk) S == (({1'b0, A} + {1'b0, B})[15:0])
    );

    // C must be the carry-out bit of the addition result.
    check_carry_out: assert property (
        @(posedge clk) C == (({1'b0, A} + {1'b0, B})[16])
    );

    // Adding zero on A must return B with no carry.
    check_a_zero_identity: assert property (
        @(posedge clk) (A == 16'h0000) |-> ({C, S} == {1'b0, B})
    );

    // Adding zero on B must return A with no carry.
    check_b_zero_identity: assert property (
        @(posedge clk) (B == 16'h0000) |-> ({C, S} == {1'b0, A})
    );

    // Disjoint 1-bits must add as XOR with no carry.
    check_disjoint_bits_xor: assert property (
        @(posedge clk) ((A & B) == 16'h0000) |-> ({C, S} == {1'b0, (A ^ B)})
    );

    // Complementary inputs must sum to all ones with no carry.
    check_complementary_inputs: assert property (
        @(posedge clk) (B == ~A) |-> ((S == 16'hFFFF) && (C == 1'b0))
    );

    // If both MSBs are 0, the addition cannot produce a carry-out.
    check_no_carry_when_msbs_zero: assert property (
        @(posedge clk) ((!A[15]) && (!B[15])) |-> (C == 1'b0)
    );

    // If both MSBs are 1, the addition must produce a carry-out.
    check_carry_when_msbs_one: assert property (
        @(posedge clk) (A[15] && B[15]) |-> (C == 1'b1)
    );

    // Adding all ones to all ones must produce FFFE with carry.
    check_all_ones_corner: assert property (
        @(posedge clk) ((A == 16'hFFFF) && (B == 16'hFFFF)) |-> ((S == 16'hFFFE) && (C == 1'b1))
    );

endmodule