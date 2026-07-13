module sky130_fd_sc_hvl__a22o_sva (
    input logic clk,
    input logic X,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic B2
);

    // X must equal the OR of the two AND terms.
    check_function_equivalence: assert property (
        @(posedge clk) X == ((A1 & A2) | (B1 & B2))
    );

    // A1 and A2 high must drive X high.
    check_a_term_sets_x: assert property (
        @(posedge clk) (A1 & A2) |-> X
    );

    // B1 and B2 high must drive X high.
    check_b_term_sets_x: assert property (
        @(posedge clk) (B1 & B2) |-> X
    );

    // With both AND terms low, X must be low.
    check_no_terms_clears_x: assert property (
        @(posedge clk) (!(A1 & A2) && !(B1 & B2)) |-> !X
    );

    // X high must come from at least one AND term.
    check_x_high_has_source: assert property (
        @(posedge clk) X |-> ((A1 & A2) || (B1 & B2))
    );

    // X low means both AND terms are low.
    check_x_low_has_no_source: assert property (
        @(posedge clk) !X |-> (!(A1 & A2) && !(B1 & B2))
    );

endmodule