module sky130_fd_sc_hvl__a22o_sva (
    input logic clk,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic B2,
    input logic X
);

    // X must match the implemented combinational equation.
    check_x_matches_boolean_function: assert property (
        @(posedge clk) X == ((A1 & A2 & ~B1 & ~B2) | (~A1 & ~A2 & B1 & B2))
    );

    // When both A inputs are high and both B inputs are low, X must be high.
    check_x_high_when_a_and_not_b: assert property (
        @(posedge clk) (A1 & A2 & ~B1 & ~B2) |-> X
    );

    // When both A inputs are low and both B inputs are high, X must be high.
    check_x_high_when_not_a_and_b: assert property (
        @(posedge clk) (~A1 & ~A2 & B1 & B2) |-> X
    );

    // When both A and B are high, X must be low.
    check_x_low_when_both_high: assert property (
        @(posedge clk) (A1 & A2 & B1 & B2) |-> !X
    );

    // When both A and B are low, X must be low.
    check_x_low_when_both_low: assert property (
        @(posedge clk) (~A1 & ~A2 & ~B1 & ~B2) |-> !X
    );

    // When A1 and B1 differ, X must be low.
    check_x_low_when_a1_xor_b1: assert property (
        @(posedge clk) (A1 ^ B1) |-> !X
    );

    // When A2 and B2 differ, X must be low.
    check_x_low_when_a2_xor_b2: assert property (
        @(posedge clk) (A2 ^ B2) |-> !X
    );

    // When A1 and A2 are equal, X must equal B1 & B2.
    check_x_equals_b_and_when_a_equal: assert property (
        @(posedge clk) (A1 == A2) |-> (X == (B1 & B2))
    );

    // When B1 and B2 are equal, X must equal A1 & A2.
    check_x_equals_a_and_when_b_equal: assert property (
        @(posedge clk) (B1 == B2) |-> (X == (A1 & A2))
    );

endmodule