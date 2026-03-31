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

    // X must match the RTL boolean equation.
    check_x_matches_rtl_equation: assert property (
        @(posedge clk)
        X == ((A && B) || (C || D) || !(E && F) || !(G || H))
    );

    // A and B high must drive X high.
    check_ab_term_sets_x: assert property (
        @(posedge clk)
        (A && B) |-> X
    );

    // C or D high must drive X high.
    check_cd_term_sets_x: assert property (
        @(posedge clk)
        (C || D) |-> X
    );

    // E and F low must drive X high.
    check_ef_term_sets_x: assert property (
        @(posedge clk)
        (!(E && F)) |-> X
    );

    // G and H low must drive X high.
    check_gh_term_sets_x: assert property (
        @(posedge clk)
        (!(G || H)) |-> X
    );

    // X must be low when all four product terms are false.
    check_x_low_when_all_terms_false: assert property (
        @(posedge clk)
        (!((A && B) || (C || D) || !(E && F) || !(G || H))) |-> !X
    );

    // X must be high when any one of the four product terms is true.
    check_x_high_when_any_term_true: assert property (
        @(posedge clk)
        ((A && B) || (C || D) || !(E && F) || !(G || H)) |-> X
    );

endmodule