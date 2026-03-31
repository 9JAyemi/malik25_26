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

    // X matches the RTL combinational equation.
    check_x_matches_rtl: assert property (
        @(posedge clk)
        X == ((A && B) || (C || D) || !(E && F) || !(G || H))
    );

    // A and B both high force X high.
    check_x_high_when_ab_high: assert property (
        @(posedge clk)
        (A && B) |-> X
    );

    // Either C or D high forces X high.
    check_x_high_when_cd_high: assert property (
        @(posedge clk)
        (C || D) |-> X
    );

    // If E and F are not both high, X must be high.
    check_x_high_when_ef_not_both_high: assert property (
        @(posedge clk)
        !(E && F) |-> X
    );

    // If G and H are both low, X must be high.
    check_x_high_when_gh_both_low: assert property (
        @(posedge clk)
        !(G || H) |-> X
    );

    // X low requires all four RTL terms to be false.
    check_x_low_implies_false_terms: assert property (
        @(posedge clk)
        !X |-> (!(A && B) && !(C || D) && (E && F) && (G || H))
    );

    // If all four RTL terms are false, X must be low.
    check_x_low_when_false_terms: assert property (
        @(posedge clk)
        (!(A && B) && !(C || D) && (E && F) && (G || H)) |-> !X
    );

endmodule