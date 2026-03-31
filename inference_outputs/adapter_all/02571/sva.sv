module sky130_fd_sc_hdll__a22o_sva (
    input logic clk,
    input logic X,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic B2
);

    // X must match the implemented AND/OR function.
    check_x_matches_a22o_function: assert property (
        @(posedge clk) X == ((A1 & A2) | (B1 & B2))
    );

    // A1 and A2 high must force X high.
    check_a_term_forces_x_high: assert property (
        @(posedge clk) (A1 & A2) |-> X
    );

    // B1 and B2 high must force X high.
    check_b_term_forces_x_high: assert property (
        @(posedge clk) (B1 & B2) |-> X
    );

    // If neither AND term is true, X must be low.
    check_no_active_term_forces_x_low: assert property (
        @(posedge clk) (!(A1 & A2) && !(B1 & B2)) |-> !X
    );

    // X high must come from at least one active AND term.
    check_x_high_has_active_term: assert property (
        @(posedge clk) X |-> ((A1 & A2) || (B1 & B2))
    );

    // X low means both AND terms are inactive.
    check_x_low_means_no_active_term: assert property (
        @(posedge clk) !X |-> (!(A1 & A2) && !(B1 & B2))
    );

endmodule