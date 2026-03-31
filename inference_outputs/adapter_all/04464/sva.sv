module four_bit_adder_sva (
    input logic [3:0] A,
    input logic [3:0] B,
    input logic [3:0] S,
    input logic Cout
);

    // S is the low 4 bits of the arithmetic sum.
    check_sum_low_bits: assert property (
        @($global_clock) S == (A + B)[3:0]
    );

    // Cout is the MSB of the arithmetic sum.
    check_cout_msb: assert property (
        @($global_clock) Cout == (A + B)[4]
    );

    // The full output matches the arithmetic sum.
    check_full_output: assert property (
        @($global_clock) {Cout, S} == (A + B)
    );

    // Adding zero on B passes A through with no carry.
    check_add_zero_b: assert property (
        @($global_clock) (B == 4'b0000) |-> ({Cout, S} == {1'b0, A})
    );

    // Adding zero on A passes B through with no carry.
    check_add_zero_a: assert property (
        @($global_clock) (A == 4'b0000) |-> ({Cout, S} == {1'b0, B})
    );

    // The maximum input pair produces 0xE with carry-out set.
    check_max_plus_max: assert property (
        @($global_clock) ((A == 4'hF) && (B == 4'hF)) |-> ({Cout, S} == 5'h1E)
    );

    // Carry-out is set exactly when the sum exceeds 4 bits.
    check_cout_threshold: assert property (
        @($global_clock) Cout == ((A + B) > 4'hF)
    );

endmodule