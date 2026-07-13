module adder_4bit_sva (
    input logic [3:0] A,
    input logic [3:0] B,
    input logic       Cin,
    input logic [3:0] S,
    input logic       Cout
);

    // Combined outputs must equal the 5-bit sum of A, B, and Cin.
    check_full_sum: assert property (
        @($global_clock)
        {Cout, S} == ({1'b0, A} + {1'b0, B} + Cin)
    );

    // S must be the low 4 bits of the combined sum.
    check_sum_bits: assert property (
        @($global_clock)
        {1'b0, S} == (({1'b0, A} + {1'b0, B} + Cin) & 5'h0F)
    );

    // Cout must be the carry-out bit of the combined sum.
    check_carry_out: assert property (
        @($global_clock)
        Cout == (({1'b0, A} + {1'b0, B} + Cin) > 5'd15)
    );

    // With B and Cin low, the adder must pass A through.
    check_pass_a_when_b_and_cin_zero: assert property (
        @($global_clock)
        ((B == 4'h0) && (Cin == 1'b0)) |-> ((S == A) && (Cout == 1'b0))
    );

    // With A and Cin low, the adder must pass B through.
    check_pass_b_when_a_and_cin_zero: assert property (
        @($global_clock)
        ((A == 4'h0) && (Cin == 1'b0)) |-> ((S == B) && (Cout == 1'b0))
    );

    // With A and B low, the adder must produce Cin on S and no carry.
    check_cin_only_when_a_and_b_zero: assert property (
        @($global_clock)
        ((A == 4'h0) && (B == 4'h0)) |-> ((S == {3'b000, Cin}) && (Cout == 1'b0))
    );

    // With A and B at 4'hF, the adder must produce 4'h0 and assert carry.
    check_max_plus_max: assert property (
        @($global_clock)
        ((A == 4'hF) && (B == 4'hF)) |-> ((S == 4'h0) && (Cout == 1'b1))
    );

endmodule