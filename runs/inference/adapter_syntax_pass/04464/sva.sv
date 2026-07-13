module four_bit_adder_sva (
    input logic [3:0] A,
    input logic [3:0] B,
    input logic [3:0] S,
    input logic Cout
);

    // S must equal the 4-bit sum of A and B.
    check_sum_matches_addition: assert property (
        @($global_clock) S == (A + B)
    );

    // Cout must be low when the 4-bit sum is less than 16.
    check_cout_low_when_sum_below_16: assert property (
        @($global_clock) ((A + B) < 5'd16) |-> (Cout == 1'b0)
    );

    // Cout must be high when the 4-bit sum is 16 or greater.
    check_cout_high_when_sum_16_or_more: assert property (
        @($global_clock) ((A + B) >= 5'd16) |-> (Cout == 1'b1)
    );

    // Cout must match the MSB of the 4-bit sum.
    check_cout_matches_sum_msb: assert property (
        @($global_clock) Cout == S[3]
    );

endmodule