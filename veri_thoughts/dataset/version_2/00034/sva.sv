module karnaugh_map_sva (
    input logic A,
    input logic B,
    input logic C,
    input logic D,
    input logic F
);

    // F must match the implemented Boolean expression.
    check_f_matches_expression: assert property (
        @($global_clock) F == (!A && (B || C))
    );

    // A high forces F low.
    check_a_high_forces_f_low: assert property (
        @($global_clock) A |-> !F
    );

    // With A low, either B or C high forces F high.
    check_b_or_c_with_a_low_sets_f: assert property (
        @($global_clock) (!A && (B || C)) |-> F
    );

    // With B and C both low, F must be low.
    check_both_b_and_c_low_clear_f: assert property (
        @($global_clock) (!B && !C) |-> !F
    );

    // If A, B, and C do not change, F must not change.
    check_f_depends_only_on_a_b_c: assert property (
        @($global_clock) ($stable(A) && $stable(B) && $stable(C)) |-> $stable(F)
    );

    // If only D changes, F must remain stable.
    check_d_change_does_not_affect_f: assert property (
        @($global_clock) ($changed(D) && $stable(A) && $stable(B) && $stable(C)) |-> $stable(F)
    );

endmodule