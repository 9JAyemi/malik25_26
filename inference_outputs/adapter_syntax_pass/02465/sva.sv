module my_module_sva (
    input logic clk,
    input logic X,
    input logic A1,
    input logic A2,
    input logic A3,
    input logic B1
);

    // X must match the RTL's combinational equation.
    check_x_matches_rtl_equation: assert property (
        @(posedge clk)
        X == (((A1 & ~A2) | (A2 & ~A1 & A3 & ~B1) | (~A1 & ~A2 & ~A3 & B1)) ? 1'b1 : 1'b0)
    );

    // A1 and A2 high must drive X high.
    check_a1_a2_high_sets_x: assert property (
        @(posedge clk)
        (A1 && A2) |-> X
    );

    // A1 and A2 low must drive X low.
    check_a1_a2_low_clears_x: assert property (
        @(posedge clk)
        (!A1 && !A2) |-> !X
    );

    // A1 high, A2 low, and A3 high must drive X high.
    check_a1_a2_low_a3_high_sets_x: assert property (
        @(posedge clk)
        (A1 && !A2 && A3) |-> X
    );

    // A1 high, A2 low, and A3 low must drive X low.
    check_a1_a2_low_a3_low_clears_x: assert property (
        @(posedge clk)
        (A1 && !A2 && !A3) |-> !X
    );

    // A1 low, A2 high, and B1 high must drive X high.
    check_a1_low_a2_high_b1_high_sets_x: assert property (
        @(posedge clk)
        (!A1 && A2 && B1) |-> X
    );

    // A1 low, A2 high, and B1 low must drive X low.
    check_a1_low_a2_high_b1_low_clears_x: assert property (
        @(posedge clk)
        (!A1 && A2 && !B1) |-> !X
    );

    // A1 low, A2 low, and B1 high must drive X low.
    check_a1_low_a2_low_b1_high_clears_x: assert property (
        @(posedge clk)
        (!A1 && !A2 && B1) |-> !X
    );

endmodule