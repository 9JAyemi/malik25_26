module subtractor_sva (
    input logic [3:0] A,
    input logic [3:0] B,
    input logic [3:0] Y
);

    // Y must equal the 4-bit difference of A and B.
    check_y_matches_difference: assert property (
        @($global_clock) Y == (A - B)
    );

    // A zero B input must leave Y equal to A.
    check_zero_b_passthrough: assert property (
        @($global_clock) (B == 4'h0) |-> (Y == A)
    );

    // A zero A input must leave Y equal to the two's complement of B.
    check_zero_a_twos_complement: assert property (
        @($global_clock) (A == 4'h0) |-> (Y == ~B + 4'h1)
    );

    // Equal inputs must produce a zero result.
    check_equal_inputs_zero: assert property (
        @($global_clock) (A == B) |-> (Y == 4'h0)
    );

    // Subtracting 1 from 0 must wrap to 15.
    check_one_minus_one_wrap: assert property (
        @($global_clock) ((A == 4'h0) && (B == 4'h1)) |-> (Y == 4'hF)
    );

    // Subtracting 15 from 1 must wrap to 0.
    check_fifteen_minus_one_wrap: assert property (
        @($global_clock) ((A == 4'h1) && (B == 4'hF)) |-> (Y == 4'h0)
    );

endmodule