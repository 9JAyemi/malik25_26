module RippleCarryAdder_sva (
    input logic       clk,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic [3:0] S,
    input logic       Cout
);

    function automatic logic carry_bit(
        input logic x,
        input logic y,
        input logic cin
    );
        carry_bit = (x & y) | (x & cin) | (y & cin);
    endfunction

    // Full 5-bit result matches A + B.
    check_sum_vector: assert property (
        @(posedge clk) {Cout, S} == ({1'b0, A} + {1'b0, B})
    );

    // Bit 0 is the XOR of A[0] and B[0].
    check_lsb_sum: assert property (
        @(posedge clk) S[0] == (A[0] ^ B[0])
    );

    // Bit 1 includes the carry from bit 0.
    check_bit1_sum: assert property (
        @(posedge clk) S[1] == (A[1] ^ B[1] ^ carry_bit(A[0], B[0], 1'b0))
    );

    // Bit 2 includes the ripple carry from lower bits.
    check_bit2_sum: assert property (
        @(posedge clk) S[2] == (A[2] ^ B[2] ^ carry_bit(A[1], B[1], carry_bit(A[0], B[0], 1'b0)))
    );

    // Bit 3 includes the ripple carry from lower bits.
    check_bit3_sum: assert property (
        @(posedge clk) S[3] == (A[3] ^ B[3] ^ carry_bit(A[2], B[2], carry_bit(A[1], B[1], carry_bit(A[0], B[0], 1'b0))))
    );

    // Cout is the final carry out of the MSB stage.
    check_final_carry: assert property (
        @(posedge clk) Cout == carry_bit(A[3], B[3], carry_bit(A[2], B[2], carry_bit(A[1], B[1], carry_bit(A[0], B[0], 1'b0))))
    );

    // Adding zero on B passes A through with no carry.
    check_b_zero_passthrough: assert property (
        @(posedge clk) (B == 4'h0) |-> ({Cout, S} == {1'b0, A})
    );

    // Adding zero on A passes B through with no carry.
    check_a_zero_passthrough: assert property (
        @(posedge clk) (A == 4'h0) |-> ({Cout, S} == {1'b0, B})
    );

    // Complementary inputs sum to all ones with no carry out.
    check_complement_case: assert property (
        @(posedge clk) (B == ~A) |-> ((S == 4'hF) && (Cout == 1'b0))
    );

endmodule