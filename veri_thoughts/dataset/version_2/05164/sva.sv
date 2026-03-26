module sky130_fd_sc_hdll__a22o_sva (
    input logic X,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic B2
);

    // X matches the implemented A22O logic function.
    check_x_matches_a22o_function: assert property (
        @($global_clock) X == ((A1 & A2) | (B1 & B2))
    );

    // A1 and A2 high must drive X high.
    check_a_term_sets_x_high: assert property (
        @($global_clock) (A1 & A2) |-> X
    );

    // B1 and B2 high must drive X high.
    check_b_term_sets_x_high: assert property (
        @($global_clock) (B1 & B2) |-> X
    );

    // If neither AND term is true, X must be low.
    check_no_active_term_drives_x_low: assert property (
        @($global_clock) (!(A1 & A2) && !(B1 & B2)) |-> !X
    );

    // X high must come from at least one active AND term.
    check_x_high_has_valid_cause: assert property (
        @($global_clock) X |-> ((A1 & A2) | (B1 & B2))
    );

endmodule