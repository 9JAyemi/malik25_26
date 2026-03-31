module logic_gate_sva (
    input logic clk,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic C1,
    input logic D1,
    input logic X
);

    // X must match the exact RTL conditional expression.
    check_x_matches_rtl_expression: assert property (
        @(posedge clk)
        X == (((A1 == 1'b1) && (A2 == 1'b0)) || ((B1 == 1'b1) && (C1 == 1'b0)) || (D1 == 1'b1))
    );

    // X must be high when A1 is high and A2 is low.
    check_x_high_for_a1_a2_condition: assert property (
        @(posedge clk)
        ((A1 == 1'b1) && (A2 == 1'b0)) |-> (X == 1'b1)
    );

    // X must be high when B1 is high and C1 is low.
    check_x_high_for_b1_c1_condition: assert property (
        @(posedge clk)
        ((B1 == 1'b1) && (C1 == 1'b0)) |-> (X == 1'b1)
    );

    // X must be high when D1 is high.
    check_x_high_for_d1_condition: assert property (
        @(posedge clk)
        (D1 == 1'b1) |-> (X == 1'b1)
    );

    // X must be low when none of the three conditions are true.
    check_x_low_when_no_conditions_true: assert property (
        @(posedge clk)
        !(((A1 == 1'b1) && (A2 == 1'b0)) || ((B1 == 1'b1) && (C1 == 1'b0)) || (D1 == 1'b1)) |-> (X == 1'b0)
    );

    // X must be low when D1 is low and the A1/A2 condition is false.
    check_x_low_when_only_d1_false: assert property (
        @(posedge clk)
        ((D1 == 1'b0) && !((A1 == 1'b1) && (A2 == 1'b0))) |-> (X == 1'b0)
    );

    // X must be low when D1 is low and the B1/C1 condition is false.
    check_x_low_when_only_b1_c1_false: assert property (
        @(posedge clk)
        ((D1 == 1'b0) && !((B1 == 1'b1) && (C1 == 1'b0))) |-> (X == 1'b0)
    );

    // X must be low when D1 is low and A1 is low.
    check_x_low_when_only_a1_low: assert property (
        @(posedge clk)
        ((D1 == 1'b0) && (A1 == 1'b0)) |-> (X == 1'b0)
    );

    // X must be low when D1 is low and A2 is high.
    check_x_low_when_only_a2_high: assert property (
        @(posedge clk)
        ((D1 == 1'b0) && (A2 == 1'b1)) |-> (X == 1'b0)
    );

    // X must be low when D1 is low and B1 is low.
    check_x_low_when_only_b1_low: assert property (
        @(posedge clk)
        ((D1 == 1'b0) && (B1 == 1'b0)) |-> (X == 1'b0)
    );

    // X must be low when D1 is low and C1 is high.
    check_x_low_when_only_c1_high: assert property (
        @(posedge clk)
        ((D1 == 1'b0) && (C1 == 1'b1)) |-> (X == 1'b0)
    );

endmodule