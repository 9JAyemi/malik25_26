module adder4_sva (
    input logic [3:0] A,
    input logic [3:0] B,
    input logic CIN,
    input logic [3:0] S,
    input logic COUT
);

    // The concatenated outputs match the 5-bit addition result.
    check_full_sum_match: assert property (
        @($global_clock) {COUT, S} == ({1'b0, A} + {1'b0, B} + CIN)
    );

    // S carries the low 4 bits of the computed sum.
    check_sum_low_bits: assert property (
        @($global_clock) {1'b0, S} == (({1'b0, A} + {1'b0, B} + CIN) & 5'h0F)
    );

    // COUT asserts exactly when the addition overflows 4 bits.
    check_carry_overflow: assert property (
        @($global_clock) COUT == (({1'b0, A} + {1'b0, B} + CIN) >= 5'd16)
    );

    // Zero inputs produce a zero output.
    check_zero_case: assert property (
        @($global_clock) (A == 4'h0 && B == 4'h0 && CIN == 1'b0) |-> ({COUT, S} == 5'h00)
    );

    // Carry-in alone increments the result when both operands are zero.
    check_cin_only_case: assert property (
        @($global_clock) (A == 4'h0 && B == 4'h0 && CIN == 1'b1) |-> ({COUT, S} == 5'h01)
    );

    // Maximum inputs produce the maximum 5-bit result.
    check_max_input_case: assert property (
        @($global_clock) (A == 4'hF && B == 4'hF && CIN == 1'b1) |-> ({COUT, S} == 5'h1F)
    );

endmodule