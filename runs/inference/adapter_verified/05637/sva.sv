module and4b_sva (
    input logic clk,
    input logic A_N,
    input logic B,
    input logic C,
    input logic D,
    input logic X
);

// X must equal the RTL expression.
    check_function_equivalence: assert property (
        @(posedge clk) X == ~(A_N | B | C | D)
    );

// A_N low forces X high.
    check_a_n_low_forces_x_high: assert property (
        @(posedge clk) !A_N |-> X
    );

// B high forces X low.
    check_b_high_forces_x_low: assert property (
        @(posedge clk) B |-> !X
    );

// C high forces X low.
    check_c_high_forces_x_low: assert property (
        @(posedge clk) C |-> !X
    );

// D high forces X low.
    check_d_high_forces_x_low: assert property (
        @(posedge clk) D |-> !X
    );

// All inputs in their low-state condition force X high.
    check_all_low_forces_x_high: assert property (
        @(posedge clk) (!A_N && !B && !C && !D) |-> X
    );

// A high X requires all inputs to be in their low-state condition.
    check_x_high_requires_all_low: assert property (
        @(posedge clk) X |-> (!A_N && !B && !C && !D)
    );

// A low X requires at least one input to be high.
    check_x_low_requires_some_high: assert property (
        @(posedge clk) !X |-> (A_N || B || C || D)
    );

endmodule
