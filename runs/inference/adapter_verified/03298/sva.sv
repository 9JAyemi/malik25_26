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
    check_output_matches_rtl: assert property (
        @(posedge clk)
        X == (( (A1 == 1'b1) && (A2 == 1'b0) ) ||
              ( (B1 == 1'b1) && (C1 == 1'b0) ) ||
              ( (D1 == 1'b1) ))
    );

// A1 high with A2 low forces X high.
    check_condition1_sets_x_high: assert property (
        @(posedge clk)
        ( (A1 == 1'b1) && (A2 == 1'b0) ) |-> (X == 1'b1)
    );

// B1 high with C1 low forces X high.
    check_condition2_sets_x_high: assert property (
        @(posedge clk)
        ( (B1 == 1'b1) && (C1 == 1'b0) ) |-> (X == 1'b1)
    );

// D1 high forces X low.
    check_condition3_sets_x_low: assert property (
        @(posedge clk)
        (D1 == 1'b1) |-> (X == 1'b0)
    );

// With no asserted conditions, X must be low.
    check_no_conditions_sets_x_low: assert property (
        @(posedge clk)
        !(( (A1 == 1'b1) && (A2 == 1'b0) ) ||
          ( (B1 == 1'b1) && (C1 == 1'b0) ) ||
          ( (D1 == 1'b1) )) |-> (X == 1'b0)
    );

// X high implies at least one of the three conditions is true.
    check_x_high_has_valid_cause: assert property (
        @(posedge clk)
        (X == 1'b1) |-> (( (A1 == 1'b1) && (A2 == 1'b0) ) ||
                         ( (B1 == 1'b1) && (C1 == 1'b0) ) ||
                         ( (D1 == 1'b1) ))
    );

// X low implies D1 is high and neither A1/A2 nor B1/C1 is active.
    check_x_low_has_valid_cause: assert property (
        @(posedge clk)
        (X == 1'b0) |-> ((D1 == 1'b1) &&
                         !((A1 == 1'b1) && (A2 == 1'b0)) &&
                         !((B1 == 1'b1) && (C1 == 1'b0)))
    );

endmodule
