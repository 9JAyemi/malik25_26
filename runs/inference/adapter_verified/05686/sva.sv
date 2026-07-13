module sky130_fd_sc_hs__a222o_sva (
    input logic clk,
    input logic X,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic B2,
    input logic C1,
    input logic C2
);

// X must match the RTL's boolean equation.
    check_x_matches_boolean_function: assert property (
        @(posedge clk) X == (((A1 & A2) | (B1 & B2) | (~C1 & ~C2)) ? 1'b1 : 1'b0)
    );

// A1 and A2 high together must drive X high.
    check_a_pair_sets_x: assert property (
        @(posedge clk) (A1 & A2) |-> X
    );

// B1 and B2 high together must drive X high.
    check_b_pair_sets_x: assert property (
        @(posedge clk) (B1 & B2) |-> X
    );

// C1 and C2 low together must drive X high.
    check_c_pair_clears_x: assert property (
        @(posedge clk) (~C1 & ~C2) |-> X
    );

// With no asserted OR term, X must be low.
    check_no_active_term_clears_x: assert property (
        @(posedge clk) !((A1 & A2) | (B1 & B2) | (~C1 & ~C2)) |-> !X
    );

// X high implies at least one OR term is asserted.
    check_x_high_has_active_term: assert property (
        @(posedge clk) X |-> ((A1 & A2) | (B1 & B2) | (~C1 & ~C2))
    );

endmodule
