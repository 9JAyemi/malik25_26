module adder4_sva (
    input logic [3:0] A,
    input logic [3:0] B,
    input logic       CIN,
    input logic [3:0] S,
    input logic       COUT
);

    // No RTL clock or reset; sample this combinational logic on the formal global clock.

    // Full 5-bit output must equal the arithmetic sum of A, B, and CIN.
    check_full_sum: assert property (
        @($global_clock) {COUT, S} == ({1'b0, A} + {1'b0, B} + CIN)
    );

    // S must match the low 4 bits of the arithmetic sum.
    check_sum_bits: assert property (
        @($global_clock) S == (({1'b0, A} + {1'b0, B} + CIN)[3:0])
    );

    // COUT must match the carry-out bit of the arithmetic sum.
    check_carry_out: assert property (
        @($global_clock) COUT == (({1'b0, A} + {1'b0, B} + CIN)[4])
    );

    // Adding zero on B with CIN low must pass A through unchanged.
    check_add_zero_b: assert property (
        @($global_clock) (B == 4'h0 && CIN == 1'b0) |-> (S == A && COUT == 1'b0)
    );

    // Adding zero on A with CIN low must pass B through unchanged.
    check_add_zero_a: assert property (
        @($global_clock) (A == 4'h0 && CIN == 1'b0) |-> (S == B && COUT == 1'b0)
    );

    // With B and CIN low, the adder must return A and no carry.
    check_pass_a_when_b_zero: assert property (
        @($global_clock) (B == 4'h0 && CIN == 1'b0) |-> (S == A && COUT == 1'b0)
    );

    // With A and CIN low, the adder must return B and no carry.
    check_pass_b_when_a_zero: assert property (
        @($global_clock) (A == 4'h0 && CIN == 1'b0) |-> (S == B && COUT == 1'b0)
    );

    // With A and B low, the adder must assert carry-out only when CIN is high.
    check_carry_only_when_cin_high: assert property (
        @($global_clock) (A == 4'h0 && B == 4'h0) |-> (COUT == CIN && S == 4'h0)
    );

    // With A and CIN low, the adder must return B and no carry.
    check_pass_b_when_a_zero_and_cin_low: assert property (
        @($global_clock) (A == 4'h0 && CIN == 1'b0) |-> (S == B && COUT == 1'b0)
    );

    // With B and CIN low, the adder must return A and no carry.
    check_pass_a_when_b_zero_and_cin_low: assert property (
        @($global_clock) (B == 4'h0 && CIN == 1'b0) |-> (S == A && COUT == 1'b0)
    );

endmodule