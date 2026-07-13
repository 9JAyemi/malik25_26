module subtractor_sva (
    input logic [3:0] A,
    input logic [3:0] B,
    input logic [3:0] Y
);

    // Y must always equal the 4-bit difference of A and B.
    check_output_matches_difference: assert property (
        @($global_clock) Y == (A - B)
    );

    // If A and B are stable, Y must remain stable.
    check_output_stable_when_inputs_stable: assert property (
        @($global_clock) ($stable(A) && $stable(B)) |-> $stable(Y)
    );

    // If only A changes while B is stable, Y must change.
    check_output_changes_with_A: assert property (
        @($global_clock) ($changed(A) && $stable(B)) |-> $changed(Y)
    );

    // If only B changes while A is stable, Y must change.
    check_output_changes_with_B: assert property (
        @($global_clock) ($changed(B) && $stable(A)) |-> $changed(Y)
    );

    // Subtracting zero on B must pass A through to Y.
    check_zero_subtractor_identity: assert property (
        @($global_clock) (B == 4'h0) |-> (Y == A)
    );

    // Subtracting equal operands must produce zero.
    check_equal_operands_zero: assert property (
        @($global_clock) (A == B) |-> (Y == 4'h0)
    );

    // Subtracting 1 from 0 must wrap around to 15.
    check_wraparound_0_minus_1: assert property (
        @($global_clock) ((A == 4'h0) && (B == 4'h1)) |-> (Y == 4'hF)
    );

    // Subtracting 1 from 1 must produce zero.
    check_wraparound_1_minus_1: assert property (
        @($global_clock) ((A == 4'h1) && (B == 4'h1)) |-> (Y == 4'h0)
    );

endmodule