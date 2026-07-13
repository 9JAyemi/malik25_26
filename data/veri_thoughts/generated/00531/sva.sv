module logic_circuit_sva (
    input logic A1,
    input logic A2,
    input logic B1,
    input logic C1,
    input logic D1,
    input logic X
);

    // X must match the implemented Boolean equation.
    check_x_matches_expression: assert property (
        @($global_clock)
        X == ((A1 & A2) | ((!A1) & B1) | ((!C1) & D1))
    );

    // The A1/A2 term is sufficient to drive X high.
    check_x_high_on_a1_a2_term: assert property (
        @($global_clock)
        (A1 & A2) |-> X
    );

    // The !A1/B1 term is sufficient to drive X high.
    check_x_high_on_not_a1_b1_term: assert property (
        @($global_clock)
        ((!A1) & B1) |-> X
    );

    // The !C1/D1 term is sufficient to drive X high.
    check_x_high_on_not_c1_d1_term: assert property (
        @($global_clock)
        ((!C1) & D1) |-> X
    );

    // X must be low when all product terms are false.
    check_x_low_when_no_term_true: assert property (
        @($global_clock)
        !((A1 & A2) | ((!A1) & B1) | ((!C1) & D1)) |-> !X
    );

    // With A1 high and the C/D term off, X reduces to A2.
    check_x_reduces_to_a2_when_a1_high: assert property (
        @($global_clock)
        (A1 & !((!C1) & D1)) |-> (X == A2)
    );

    // With A1 low and the C/D term off, X reduces to B1.
    check_x_reduces_to_b1_when_a1_low: assert property (
        @($global_clock)
        ((!A1) & !((!C1) & D1)) |-> (X == B1)
    );

endmodule