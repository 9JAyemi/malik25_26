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

// X must match the RTL Boolean equation.
    check_x_equation: assert property (
        @(posedge clk) X == ((A & B) | (C | D) | !(E & F) | !(G | H))
    );

// A and B high must force X high.
    check_and0_forces_x_high: assert property (
        @(posedge clk) (A && B) |-> X
    );

// C or D high must force X high.
    check_or0_forces_x_high: assert property (
        @(posedge clk) (C || D) |-> X
    );

// E and F low must force X high.
    check_and1_low_forces_x_high: assert property (
        @(posedge clk) (!E && !F) |-> X
    );

// G or H high must force X high.
    check_or1_low_forces_x_high: assert property (
        @(posedge clk) (!G && !H) |-> X
    );

// With all terms inactive, X must be low.
    check_all_terms_inactive_forces_x_low: assert property (
        @(posedge clk) (!(A && B) && !(C || D) && (E && F) && (G || H)) |-> !X
    );

endmodule
