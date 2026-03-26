module four_input_gate_assertions (
    input logic clk,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic C1,
    input logic X
);

    // X must match the RTL boolean equation.
    check_boolean_equation: assert property (
        @(posedge clk)
        X == ((A1 & A2) | (~A1 & B1) | (~A1 & ~B1 & C1))
    );

    // When A1 is high, X follows A2.
    check_a1_high_selects_a2: assert property (
        @(posedge clk)
        (A1 == 1'b1) |-> (X == A2)
    );

    // When A1 is low and B1 is high, X is high.
    check_a1_low_b1_high_forces_high: assert property (
        @(posedge clk)
        ((A1 == 1'b0) && (B1 == 1'b1)) |-> (X == 1'b1)
    );

    // When A1 and B1 are low, X follows C1.
    check_a1_low_b1_low_selects_c1: assert property (
        @(posedge clk)
        ((A1 == 1'b0) && (B1 == 1'b0)) |-> (X == C1)
    );

    // When A1 is high and A2 is low, X is low.
    check_a1_high_a2_low_drives_low: assert property (
        @(posedge clk)
        ((A1 == 1'b1) && (A2 == 1'b0)) |-> (X == 1'b0)
    );

endmodule