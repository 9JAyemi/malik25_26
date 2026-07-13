module logic_module_sva (
    input logic clk,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic B2,
    input logic VPWR,
    input logic VGND,
    input logic X
);

    // X must match the RTL boolean equation.
    check_output_matches_rtl_equation: assert property (
        @(posedge clk)
        X == ((A1 | A2) & (~B1 | B2) & (~A1 | ~A2 | B1))
    );

    // With B1 low, X reduces to A1 xor A2.
    check_x_equals_xor_when_b1_low: assert property (
        @(posedge clk)
        (!B1) |-> (X == (A1 ^ A2))
    );

    // With B1 high, X reduces to B2 and (A1 or A2).
    check_x_equals_b2_and_a_or_when_b1_high: assert property (
        @(posedge clk)
        B1 |-> (X == (B2 & (A1 | A2)))
    );

    // If both A inputs are low, X must be low.
    check_x_low_when_both_a_low: assert property (
        @(posedge clk)
        (!A1 && !A2) |-> (X == 1'b0)
    );

    // If B1 is high and B2 is low, X must be low.
    check_x_low_when_b1_high_b2_low: assert property (
        @(posedge clk)
        (B1 && !B2) |-> (X == 1'b0)
    );

    // If B1 and B2 are high and any A input is high, X must be high.
    check_x_high_when_b1_b2_high_and_any_a_high: assert property (
        @(posedge clk)
        (B1 && B2 && (A1 || A2)) |-> (X == 1'b1)
    );

endmodule