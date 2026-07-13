module sky130_fd_sc_ls__a222o_sva (
    input logic clk,
    input logic X,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic B2,
    input logic C1,
    input logic C2
);

    // X matches the implemented OR-of-ANDs function.
    check_x_matches_or_of_ands: assert property (
        @(posedge clk) X == ((A1 & A2) | (B1 & B2) | (C1 & C2))
    );

    // A1 and A2 high forces X high.
    check_a_term_sets_x: assert property (
        @(posedge clk) (A1 & A2) |-> X
    );

    // B1 and B2 high forces X high.
    check_b_term_sets_x: assert property (
        @(posedge clk) (B1 & B2) |-> X
    );

    // C1 and C2 high forces X high.
    check_c_term_sets_x: assert property (
        @(posedge clk) (C1 & C2) |-> X
    );

    // X can only be high when at least one product term is high.
    check_x_high_requires_some_term: assert property (
        @(posedge clk) X |-> ((A1 & A2) | (B1 & B2) | (C1 & C2))
    );

    // X can only be low when all three product terms are low.
    check_x_low_requires_all_terms_low: assert property (
        @(posedge clk) !X |-> !(A1 & A2) && !(B1 & B2) && !(C1 & C2)
    );

endmodule