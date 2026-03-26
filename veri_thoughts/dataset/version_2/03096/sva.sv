module logic_module_sva (
    input logic A1,
    input logic A2,
    input logic B1,
    input logic B2,
    input logic Y
);

    // Y must match the RTL combinational expression.
    check_y_matches_rtl: assert property (
        @($global_clock)
        Y == ((A1 & A2) |
              ((A1 & ~B1 & ~B2) & ~(A2 | B1 | B2)) |
              (~A1 & ~A2 & B1 & B2))
    );

    // A1 and A2 high forces Y high.
    check_y_high_when_a1_a2_high: assert property (
        @($global_clock)
        (A1 && A2) |-> Y
    );

    // A1 high with A2 low and both B inputs low forces Y high.
    check_y_high_when_a1_only_and_b_low: assert property (
        @($global_clock)
        (A1 && !A2 && !B1 && !B2) |-> Y
    );

    // Both A inputs low and both B inputs high forces Y high.
    check_y_high_when_a_low_and_b_high: assert property (
        @($global_clock)
        (!A1 && !A2 && B1 && B2) |-> Y
    );

    // A1 low with A2 high forces Y low.
    check_y_low_when_a1_low_a2_high: assert property (
        @($global_clock)
        (!A1 && A2) |-> !Y
    );

    // A1 high with A2 low and any B input high forces Y low.
    check_y_low_when_a1_high_a2_low_and_any_b_high: assert property (
        @($global_clock)
        (A1 && !A2 && (B1 || B2)) |-> !Y
    );

    // Both A inputs low require both B inputs high for Y to be high.
    check_y_low_when_a_low_without_b_pair: assert property (
        @($global_clock)
        (!A1 && !A2 && !(B1 && B2)) |-> !Y
    );

    // If Y is high while A1 is low, it must come from the B1/B2 term.
    check_y_high_with_a1_low_implies_b_term: assert property (
        @($global_clock)
        (Y && !A1) |-> (!A2 && B1 && B2)
    );

    // If Y is high while A1 is high and A2 is low, both B inputs must be low.
    check_y_high_with_a1_high_a2_low_implies_b_low: assert property (
        @($global_clock)
        (Y && A1 && !A2) |-> (!B1 && !B2)
    );

endmodule