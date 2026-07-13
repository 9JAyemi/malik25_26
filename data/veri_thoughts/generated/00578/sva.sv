module combinational_circuit_sva (
    input logic X,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic C1
);
    // No explicit clock/reset in RTL; pure combinational; assertions use $global_clock.
    // Behavior: priority-if chain: A1?1 : A2?0 : B1?1 : C1?0 : 1.

    // A1 high forces X high (top priority).
    check_a1_forces_one: assert property (
        @($global_clock) (A1 == 1'b1) |-> (X == 1'b1)
    );

    // With A1 low and A2 high, X is driven low.
    check_a2_sets_zero_when_a1_low: assert property (
        @($global_clock) ((A1 == 1'b0) && (A2 == 1'b1)) |-> (X == 1'b0)
    );

    // With A1,A2 low and B1 high, X is driven high.
    check_b1_sets_one_when_a1_a2_low: assert property (
        @($global_clock) ((A1 == 1'b0) && (A2 == 1'b0) && (B1 == 1'b1)) |-> (X == 1'b1)
    );

    // With A1,A2,B1 low and C1 high, X is driven low.
    check_c1_sets_zero_when_higher_low: assert property (
        @($global_clock) ((A1 == 1'b0) && (A2 == 1'b0) && (B1 == 1'b0) && (C1 == 1'b1)) |-> (X == 1'b0)
    );

    // With all inputs low, default drives X high.
    check_default_sets_one: assert property (
        @($global_clock) ((A1 == 1'b0) && (A2 == 1'b0) && (B1 == 1'b0) && (C1 == 1'b0)) |-> (X == 1'b1)
    );

    // When both B1 and C1 high and higher terms low, B1 overrides -> X high.
    check_b1_overrides_c1: assert property (
        @($global_clock) ((A1 == 1'b0) && (A2 == 1'b0) && (B1 == 1'b1) && (C1 == 1'b1)) |-> (X == 1'b1)
    );

    // When A1 and A2 are high, A1 overrides -> X high.
    check_a1_overrides_a2: assert property (
        @($global_clock) ((A1 == 1'b1) && (A2 == 1'b1)) |-> (X == 1'b1)
    );

    // When A1 and C1 are high, A1 overrides -> X high.
    check_a1_overrides_c1: assert property (
        @($global_clock) ((A1 == 1'b1) && (C1 == 1'b1)) |-> (X == 1'b1)
    );

    // X low occurs only via A2 path or C1 path with higher terms low.
    check_zero_only_in_a2_or_c1_paths: assert property (
        @($global_clock) (X == 1'b0) |-> ((A1 == 1'b0) && ((A2 == 1'b1) || ((A2 == 1'b0) && (B1 == 1'b0) && (C1 == 1'b1))))
    );

    // If X is high and A1 is low, then A2 must be low (else A2-branch would force X low).
    check_x_high_implies_a2_low_when_a1_low: assert property (
        @($global_clock) ((X == 1'b1) && (A1 == 1'b0)) |-> (A2 == 1'b0)
    );

endmodule