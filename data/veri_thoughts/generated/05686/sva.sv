module sky130_fd_sc_hs__a222o_sva (
    input logic X,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic B2,
    input logic C1,
    input logic C2
);

    // X must match the implemented combinational function.
    check_x_matches_function: assert property (
        @($global_clock)
        X === ((((A1 & A2) | (B1 & B2) | (~C1 & ~C2)) ? 1'b1 : 1'b0))
    );

    // The A input product term drives X high.
    check_a_term_drives_high: assert property (
        @($global_clock)
        ((A1 & A2) === 1'b1) |-> (X === 1'b1)
    );

    // The B input product term drives X high.
    check_b_term_drives_high: assert property (
        @($global_clock)
        ((B1 & B2) === 1'b1) |-> (X === 1'b1)
    );

    // Both C inputs low drive X high.
    check_c_term_drives_high: assert property (
        @($global_clock)
        ((~C1 & ~C2) === 1'b1) |-> (X === 1'b1)
    );

    // X must be low when all three terms are false.
    check_no_true_term_drives_low: assert property (
        @($global_clock)
        (((A1 & A2) | (B1 & B2) | (~C1 & ~C2)) === 1'b0) |-> (X === 1'b0)
    );

endmodule