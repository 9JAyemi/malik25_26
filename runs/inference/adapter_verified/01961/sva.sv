module and3_not_A_sva (
    input logic clk,
    input logic A,
    input logic B,
    input logic C,
    input logic X
);

// X must match the RTL expression.
    check_functional_equivalence: assert property (
        @(posedge clk) X == (~A) & B & C
    );

// A high forces X low.
    check_a_high_forces_x_low: assert property (
        @(posedge clk) A |-> !X
    );

// B low forces X low.
    check_b_low_forces_x_low: assert property (
        @(posedge clk) !B |-> !X
    );

// C low forces X low.
    check_c_low_forces_x_low: assert property (
        @(posedge clk) !C |-> !X
    );

// With A low, B high, and C high, X must be high.
    check_all_conditions_drive_x_high: assert property (
        @(posedge clk) (!A && B && C) |-> X
    );

// X high implies A is low and B and C are high.
    check_x_high_implies_inputs: assert property (
        @(posedge clk) X |-> (!A && B && C)
    );

endmodule
