module four_bit_adder_sva (
    input logic [3:0] A,
    input logic [3:0] B,
    input logic Cin,
    input logic [3:0] S,
    input logic Cout
);

    // Combined output matches the 5-bit sum of A, B, and Cin.
    check_total_sum: assert property (
        @($global_clock)
        {Cout, S} == ({1'b0, A} + {1'b0, B} + {4'b0, Cin})
    );

    // The least-significant sum bit is the XOR of the least-significant inputs and carry-in.
    check_lsb_sum: assert property (
        @($global_clock)
        S[0] == (A[0] ^ B[0] ^ Cin)
    );

    // With B and Cin low, the adder passes A through unchanged.
    check_pass_a: assert property (
        @($global_clock)
        ((B == 4'h0) && (Cin == 1'b0)) |-> ({Cout, S} == {1'b0, A})
    );

    // With A and Cin low, the adder passes B through unchanged.
    check_pass_b: assert property (
        @($global_clock)
        ((A == 4'h0) && (Cin == 1'b0)) |-> ({Cout, S} == {1'b0, B})
    );

    // With both operands zero, the result is just Cin.
    check_zero_operands: assert property (
        @($global_clock)
        ((A == 4'h0) && (B == 4'h0)) |-> ({Cout, S} == {4'b0000, Cin})
    );

    // Adding 1 to 4'hF produces a full carry chain and 5'h10.
    check_full_carry_chain: assert property (
        @($global_clock)
        ((A == 4'hF) && (B == 4'h0) && (Cin == 1'b1)) |-> ({Cout, S} == 5'h10)
    );

    // The maximum input combination produces 5'h1F.
    check_max_addition: assert property (
        @($global_clock)
        ((A == 4'hF) && (B == 4'hF) && (Cin == 1'b1)) |-> ({Cout, S} == 5'h1F)
    );

endmodule