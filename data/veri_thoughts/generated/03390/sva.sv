module signal_combiner_sva (
    input logic A1,
    input logic A2,
    input logic A3,
    input logic B1,
    input logic B2,
    input logic X
);

    // X must match the implemented OR-of-products equation.
    check_output_equation: assert property (
        @($global_clock) X == ((A1 & A2) | (A3 & B1) | (B1 & B2))
    );

    // The A1&A2 product term must force X high.
    check_a1_a2_term: assert property (
        @($global_clock) (A1 & A2) |-> X
    );

    // The A3&B1 product term must force X high.
    check_a3_b1_term: assert property (
        @($global_clock) (A3 & B1) |-> X
    );

    // The B1&B2 product term must force X high.
    check_b1_b2_term: assert property (
        @($global_clock) (B1 & B2) |-> X
    );

    // If X is high, at least one product term must be high.
    check_output_high_has_source: assert property (
        @($global_clock) X |-> ((A1 & A2) | (A3 & B1) | (B1 & B2))
    );

    // If no product term is high, X must be low.
    check_no_term_low_output: assert property (
        @($global_clock) (!((A1 & A2) | (A3 & B1) | (B1 & B2))) |-> !X
    );

    // With B1 low, X reduces to the A1&A2 term only.
    check_b1_low_reduction: assert property (
        @($global_clock) (!B1) |-> (X == (A1 & A2))
    );

endmodule