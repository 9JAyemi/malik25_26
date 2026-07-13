module adder4_sva (
    input logic [3:0] A,
    input logic [3:0] B,
    input logic       CIN,
    input logic [3:0] S,
    input logic       COUT
);

    // No RTL clock or reset; sample this combinational logic on the formal global clock.

    // S must equal the low 4 bits of A + B + CIN.
    check_sum_matches_addition: assert property (
        @($global_clock) S == (A + B + CIN)
    );

    // COUT must equal the carry-out of A + B + CIN.
    check_cout_matches_addition: assert property (
        @($global_clock) COUT == (({1'b0, A} + {1'b0, B} + CIN) >= 5'd16)
    );

    // The 5-bit result must equal A + B + CIN.
    check_full_result_matches_addition: assert property (
        @($global_clock) {COUT, S} == ({1'b0, A} + {1'b0, B} + CIN)
    );

    // With B and CIN low, the adder must pass A through.
    check_a_passthrough_when_b_and_cin_zero: assert property (
        @($global_clock) (B == 4'h0 && CIN == 1'b0) |-> (S == A && COUT == 1'b0)
    );

    // With A and CIN low, the adder must pass B through.
    check_b_passthrough_when_a_and_cin_zero: assert property (
        @($global_clock) (A == 4'h0 && CIN == 1'b0) |-> (S == B && COUT == 1'b0)
    );

    // With A and B low, the adder must produce CIN on S.
    check_cin_passthrough_when_a_and_b_zero: assert property (
        @($global_clock) (A == 4'h0 && B == 4'h0) |-> (S == {3'b000, CIN} && COUT == 1'b0)
    );

    // With A and B at 4'hF, the adder must produce 4'h0 on S and assert COUT.
    check_full_carry_when_a_and_b_max: assert property (
        @($global_clock) (A == 4'hF && B == 4'hF) |-> (S == 4'h0 && COUT == 1'b1)
    );

endmodule