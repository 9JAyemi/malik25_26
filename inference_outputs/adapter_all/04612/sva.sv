module logic_module_sva (
    input logic clk,
    input logic A,
    input logic B,
    input logic C,
    input logic D,
    input logic E,
    input logic F,
    input logic G,
    input logic H,
    input logic X
);

    // X must match the implemented combinational equation.
    check_x_matches_logic: assert property (
        @(posedge clk) X == ((A & B) || (C | D) || !(E & F) || !(G | H))
    );

    // A and B high must force X high.
    check_ab_term_sets_x: assert property (
        @(posedge clk) (A & B) |-> X
    );

    // C or D high must force X high.
    check_cd_term_sets_x: assert property (
        @(posedge clk) (C | D) |-> X
    );

    // E and F low must force X high.
    check_ef_term_sets_x: assert property (
        @(posedge clk) !(E & F) |-> X
    );

    // G or H low must force X high.
    check_gh_term_sets_x: assert property (
        @(posedge clk) !(G | H) |-> X
    );

    // If all four product terms are false, X must be low.
    check_all_terms_false_clears_x: assert property (
        @(posedge clk) !((A & B) || (C | D) || !(E & F) || !(G | H)) |-> !X
    );

    // X low means every product term must be false.
    check_x_low_requires_all_terms_false: assert property (
        @(posedge clk) !X |-> !((A & B) || (C | D) || !(E & F) || !(G | H))
    );

    // X high means at least one product term must be true.
    check_x_high_requires_some_term_true: assert property (
        @(posedge clk) X |-> ((A & B) || (C | D) || !(E & F) || !(G | H))
    );

endmodule