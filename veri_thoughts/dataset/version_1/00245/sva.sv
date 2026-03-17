module sky130_fd_sc_ls__a311o_sva (
    input logic X,
    input logic A1,
    input logic A2,
    input logic A3,
    input logic B1,
    input logic C1
);

    // X implements the OR of B1, C1, and the three-input AND term.
    check_x_matches_logic_function: assert property (
        @($global_clock) X == ((A1 & A2 & A3) | B1 | C1)
    );

    // B1 alone is sufficient to drive X high.
    check_b1_forces_x_high: assert property (
        @($global_clock) B1 |-> X
    );

    // C1 alone is sufficient to drive X high.
    check_c1_forces_x_high: assert property (
        @($global_clock) C1 |-> X
    );

    // All three A inputs high are sufficient to drive X high.
    check_and_term_forces_x_high: assert property (
        @($global_clock) (A1 & A2 & A3) |-> X
    );

    // With B1 and C1 low, X reduces to the A1/A2/A3 AND term.
    check_x_equals_and_term_when_b1_c1_low: assert property (
        @($global_clock) (!B1 && !C1) |-> (X == (A1 & A2 & A3))
    );

    // If all OR inputs are low, X must be low.
    check_x_low_when_all_or_terms_low: assert property (
        @($global_clock) (!B1 && !C1 && !(A1 & A2 & A3)) |-> !X
    );

    // If X is high while B1 and C1 are low, it must come from the AND term.
    check_x_high_without_b1_c1_requires_and_term: assert property (
        @($global_clock) (X && !B1 && !C1) |-> (A1 & A2 & A3)
    );

endmodule