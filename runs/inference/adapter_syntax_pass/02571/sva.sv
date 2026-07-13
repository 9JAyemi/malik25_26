module sky130_fd_sc_hdll__a22o_sva (
    input logic clk,
    input logic X,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic B2
);

    // X must equal the OR of the two AND terms.
    check_x_matches_or_of_ands: assert property (
        @(posedge clk) X == ((A1 & A2) | (B1 & B2))
    );

    // A1 and A2 high must drive X high.
    check_a_term_drives_x_high: assert property (
        @(posedge clk) (A1 & A2) |-> X
    );

    // B1 and B2 high must drive X high.
    check_b_term_drives_x_high: assert property (
        @(posedge clk) (B1 & B2) |-> X
    );

    // With both AND terms low, X must be low.
    check_no_active_term_means_x_low: assert property (
        @(posedge clk) (!(A1 & A2) && !(B1 & B2)) |-> !X
    );

    // X high must come from at least one active AND term.
    check_x_high_has_active_source: assert property (
        @(posedge clk) X |-> ((A1 & A2) || (B1 & B2))
    );

endmodule