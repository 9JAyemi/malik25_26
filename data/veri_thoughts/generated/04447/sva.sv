module sky130_fd_sc_hvl__and3_sva (
    input logic X,
    input logic A,
    input logic B,
    input logic C
);

    // X matches the 3-input AND of A, B, and C.
    check_and_equivalence: assert property (
        @($global_clock) X == (A & B & C)
    );

    // X can be high only when all inputs are high.
    check_x_high_implies_all_inputs_high: assert property (
        @($global_clock) X |-> (A && B && C)
    );

    // All high inputs must drive X high.
    check_all_inputs_high_drive_x_high: assert property (
        @($global_clock) (A && B && C) |-> X
    );

    // Any low input must force X low.
    check_any_low_forces_x_low: assert property (
        @($global_clock) (!A || !B || !C) |-> !X
    );

    // With A and B high, X must match C.
    check_c_controls_x_when_a_b_high: assert property (
        @($global_clock) (A && B) |-> (X == C)
    );

    // With A and C high, X must match B.
    check_b_controls_x_when_a_c_high: assert property (
        @($global_clock) (A && C) |-> (X == B)
    );

    // With B and C high, X must match A.
    check_a_controls_x_when_b_c_high: assert property (
        @($global_clock) (B && C) |-> (X == A)
    );

    // Stable inputs must keep X stable.
    check_stable_inputs_keep_x_stable: assert property (
        @($global_clock) (!$initstate && $stable({A, B, C})) |-> $stable(X)
    );

endmodule