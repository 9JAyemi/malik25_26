module signal_combiner_sva (
    input logic A1,
    input logic A2,
    input logic B1,
    input logic B2,
    input logic C1,
    input logic Y,
    input logic VPWR,
    input logic VGND
);

    // Y must match the implemented combinational expression.
    check_y_matches_combiner_function: assert property (
        @($global_clock) Y == ((A1 & A2) | (B1 & B2) | C1)
    );

    // C1 alone is sufficient to drive Y high.
    check_c1_forces_y_high: assert property (
        @($global_clock) C1 |-> Y
    );

    // A1 and A2 high together are sufficient to drive Y high.
    check_a_term_forces_y_high: assert property (
        @($global_clock) (A1 & A2) |-> Y
    );

    // B1 and B2 high together are sufficient to drive Y high.
    check_b_term_forces_y_high: assert property (
        @($global_clock) (B1 & B2) |-> Y
    );

    // Y must be low when all three contributing terms are low.
    check_y_low_when_all_terms_low: assert property (
        @($global_clock) (!C1 && !(A1 & A2) && !(B1 & B2)) |-> !Y
    );

    // A high Y must come from at least one implemented term.
    check_y_high_requires_active_term: assert property (
        @($global_clock) Y |-> (C1 || (A1 & A2) || (B1 & B2))
    );

    // Without C1 and the B term, a high Y must come from the A term.
    check_y_high_without_c1_or_b_term_requires_a_term: assert property (
        @($global_clock) (Y && !C1 && !(B1 & B2)) |-> (A1 & A2)
    );

    // Without C1 and the A term, a high Y must come from the B term.
    check_y_high_without_c1_or_a_term_requires_b_term: assert property (
        @($global_clock) (Y && !C1 && !(A1 & A2)) |-> (B1 & B2)
    );

endmodule