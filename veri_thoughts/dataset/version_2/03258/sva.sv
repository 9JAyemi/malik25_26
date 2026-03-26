module ripple_carry_adder_sva (
    input logic       clk,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic [3:0] S,
    input logic       Cout
);

    // The 4-bit adder output must equal A + B with zero carry-in.
    check_total_sum: assert property (
        @(posedge clk) {Cout, S} == ({1'b0, A} + {1'b0, B})
    );

    // Bit 0 sum is the XOR of A[0] and B[0] because the initial carry-in is 0.
    check_lsb_sum: assert property (
        @(posedge clk) S[0] == (A[0] ^ B[0])
    );

    // Without a carry from bit 0, the upper bits sum without an added carry-in.
    check_upper_sum_without_bit0_carry: assert property (
        @(posedge clk) !(A[0] & B[0]) |-> ({Cout, S[3:1]} == ({1'b0, A[3:1]} + {1'b0, B[3:1]}))
    );

    // With a carry from bit 0, the upper bits sum includes a carry-in of 1.
    check_upper_sum_with_bit0_carry: assert property (
        @(posedge clk) (A[0] & B[0]) |-> ({Cout, S[3:1]} == ({1'b0, A[3:1]} + {1'b0, B[3:1]} + 4'd1))
    );

    // A value of zero on A passes B through unchanged with no overflow.
    check_zero_a_passthrough: assert property (
        @(posedge clk) (A == 4'b0000) |-> ({Cout, S} == {1'b0, B})
    );

    // A value of zero on B passes A through unchanged with no overflow.
    check_zero_b_passthrough: assert property (
        @(posedge clk) (B == 4'b0000) |-> ({Cout, S} == {1'b0, A})
    );

    // When A and B have no overlapping 1s, the result is their XOR with no carry-out.
    check_disjoint_inputs_xor: assert property (
        @(posedge clk) ((A & B) == 4'b0000) |-> ({Cout, S} == {1'b0, (A ^ B)})
    );

    // Adding 1 to 4'hF must ripple a carry through all four stages.
    check_full_ripple_propagation: assert property (
        @(posedge clk) (((A == 4'hF) && (B == 4'h1)) || ((A == 4'h1) && (B == 4'hF))) |-> ({Cout, S} == 5'h10)
    );

    // The maximum input pair must produce the expected overflowed sum.
    check_max_plus_max: assert property (
        @(posedge clk) ((A == 4'hF) && (B == 4'hF)) |-> ({Cout, S} == 5'h1E)
    );

endmodule