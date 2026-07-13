module logic_gate_sva (
    input logic clk,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic C1,
    input logic D1,
    input logic X
);

    // X must match the RTL's nested conditional expression.
    check_x_matches_rtl_expression: assert property (
        @(posedge clk)
        X == (((A1 == 1'b1) && (A2 == 1'b0)) ||
              ((B1 == 1'b1) && (C1 == 1'b0)) ||
              (D1 == 1'b1))
    );

    // D1 high must force X low.
    check_d1_forces_x_low: assert property (
        @(posedge clk)
        (D1 == 1'b1) |-> (X == 1'b0)
    );

    // A1 high and A2 low must force X high.
    check_a1_a2_condition_sets_x_high: assert property (
        @(posedge clk)
        ((A1 == 1'b1) && (A2 == 1'b0)) |-> (X == 1'b1)
    );

    // B1 high and C1 low must force X high.
    check_b1_c1_condition_sets_x_high: assert property (
        @(posedge clk)
        ((B1 == 1'b1) && (C1 == 1'b0)) |-> (X == 1'b1)
    );

    // With no active condition, X must be low.
    check_no_active_condition_sets_x_low: assert property (
        @(posedge clk)
        (!((A1 == 1'b1) && (A2 == 1'b0)) &&
         !((B1 == 1'b1) && (C1 == 1'b0)) &&
         (D1 == 1'b0)) |-> (X == 1'b0)
    );

    // X high must come from one of the implemented conditions.
    check_x_high_has_valid_source: assert property (
        @(posedge clk)
        (X == 1'b1) |-> (((A1 == 1'b1) && (A2 == 1'b0)) ||
                         ((B1 == 1'b1) && (C1 == 1'b0)) ||
                         (D1 == 1'b1))
    );

endmodule