module sky130_fd_sc_hvl__a22o_sva (
    input logic clk,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic B2,
    input logic X
);

    // X must match the RTL Boolean equation.
    check_x_matches_rtl_equation: assert property (
        @(posedge clk)
        X == ((A1 & A2 & ~B1 & ~B2) | (~A1 & ~A2 & B1 & B2))
    );

    // When both A inputs are high and both B inputs are low, X must be high.
    check_x_high_when_a1_a2_high_and_b1_b2_low: assert property (
        @(posedge clk)
        (A1 & A2 & ~B1 & ~B2) |-> X
    );

    // When both A inputs are low and both B inputs are high, X must be high.
    check_x_high_when_a1_a2_low_and_b1_b2_high: assert property (
        @(posedge clk)
        (~A1 & ~A2 & B1 & B2) |-> X
    );

    // When the A and B input patterns do not match, X must be low.
    check_x_low_when_inputs_do_not_match: assert property (
        @(posedge clk)
        (!((A1 & A2 & ~B1 & ~B2) | (~A1 & ~A2 & B1 & B2))) |-> !X
    );

endmodule