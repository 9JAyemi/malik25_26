module signal_combiner_sva (
    input logic A1,
    input logic A2,
    input logic A3,
    input logic B1,
    input logic C1,
    input logic Y
);

    // Y must match the implemented priority-combine equation.
    check_y_equation: assert property (
        @($global_clock)
        Y == (A1 ? 1'b1 : (A2 ? B1 : (A3 ? C1 : 1'b0)))
    );

    // A1 has highest priority and forces Y high.
    check_a1_priority: assert property (
        @($global_clock)
        A1 |-> (Y == 1'b1)
    );

    // With A1 low, A2 selects B1 onto Y.
    check_a2_selects_b1: assert property (
        @($global_clock)
        (!A1 && A2) |-> (Y == B1)
    );

    // With A1 and A2 low, A3 selects C1 onto Y.
    check_a3_selects_c1: assert property (
        @($global_clock)
        (!A1 && !A2 && A3) |-> (Y == C1)
    );

    // With all select inputs low, Y must be low.
    check_default_zero: assert property (
        @($global_clock)
        (!A1 && !A2 && !A3) |-> (Y == 1'b0)
    );

endmodule