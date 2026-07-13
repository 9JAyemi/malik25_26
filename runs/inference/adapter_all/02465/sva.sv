module my_module_sva (
    input logic clk,
    input logic X,
    input logic A1,
    input logic A2,
    input logic A3,
    input logic B1
);

    // X matches the exact RTL boolean expression.
    check_x_matches_rtl_expression: assert property (
        @(posedge clk)
        X == (((A1 & ~A2) | (A2 & ~A1 & A3 & ~B1) | (~A1 & ~A2 & ~A3 & B1)) ? 1'b1 : 1'b0)
    );

    // A1 high with A2 low forces X high.
    check_x_high_when_a1_high_a2_low: assert property (
        @(posedge clk)
        (A1 & ~A2) |-> X
    );

    // A2 high with A1 low and A3 high with B1 low forces X high.
    check_x_high_when_a2_high_a1_low_a3_high_b1_low: assert property (
        @(posedge clk)
        (A2 & ~A1 & A3 & ~B1) |-> X
    );

    // All A inputs low with B1 high forces X high.
    check_x_high_when_all_a_low_b1_high: assert property (
        @(posedge clk)
        (~A1 & ~A2 & ~A3 & B1) |-> X
    );

    // With A1 and A2 high, X must be low.
    check_x_low_when_a1_a2_high: assert property (
        @(posedge clk)
        (A1 & A2) |-> ~X
    );

    // With A1 and A2 low, X must be low.
    check_x_low_when_a1_a2_low: assert property (
        @(posedge clk)
        (~A1 & ~A2) |-> ~X
    );

    // With A1 and A3 high, X must be low.
    check_x_low_when_a1_a3_high: assert property (
        @(posedge clk)
        (A1 & A3) |-> ~X
    );

    // With A2 and A3 high, X must be low.
    check_x_low_when_a2_a3_high: assert property (
        @(posedge clk)
        (A2 & A3) |-> ~X
    );

    // With A1 and B1 high, X must be low.
    check_x_low_when_a1_b1_high: assert property (
        @(posedge clk)
        (A1 & B1) |-> ~X
    );

    // With A2 and B1 high, X must be low.
    check_x_low_when_a2_b1_high: assert property (
        @(posedge clk)
        (A2 & B1) |-> ~X
    );

    // With A3 and B1 high, X must be low.
    check_x_low_when_a3_b1_high: assert property (
        @(posedge clk)
        (A3 & B1) |-> ~X
    );

endmodule