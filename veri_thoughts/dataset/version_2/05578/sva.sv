module sky130_fd_sc_lp__a22o_sva (
    input logic X,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic B2
);

    // X implements (A1 & A2) | (B1 & B2).
    check_output_function: assert property (
        @($global_clock) X == ((A1 && A2) || (B1 && B2))
    );

    // A1 and A2 high force X high.
    check_a_term_drives_output: assert property (
        @($global_clock) (A1 && A2) |-> X
    );

    // B1 and B2 high force X high.
    check_b_term_drives_output: assert property (
        @($global_clock) (B1 && B2) |-> X
    );

    // If neither AND term is true, X must be low.
    check_no_terms_means_low: assert property (
        @($global_clock) (!(A1 && A2) && !(B1 && B2)) |-> !X
    );

    // A high X must come from at least one AND term.
    check_high_output_has_source: assert property (
        @($global_clock) X |-> ((A1 && A2) || (B1 && B2))
    );

    // If X is high and the A term is low, the B term must be high.
    check_high_output_requires_b_when_a_low: assert property (
        @($global_clock) (X && !(A1 && A2)) |-> (B1 && B2)
    );

    // If X is high and the B term is low, the A term must be high.
    check_high_output_requires_a_when_b_low: assert property (
        @($global_clock) (X && !(B1 && B2)) |-> (A1 && A2)
    );

endmodule