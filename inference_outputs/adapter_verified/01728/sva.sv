module mult_select_sva (
    input logic clk,
    input logic X,
    input logic A1,
    input logic A2,
    input logic B1_N
);

// X matches the RTL combinational equation.
    check_function_equivalence: assert property (
        @(posedge clk) X == ((A1 & A2 & ~B1_N) | (~A1 & (A2 | B1_N)))
    );

// When A1 and A2 are both high and B1_N is low, X must be high.
    check_select_high: assert property (
        @(posedge clk) (A1 && A2 && !B1_N) |-> X
    );

// When A1 is low, X must be high regardless of A2 and B1_N.
    check_a1_low_forces_high: assert property (
        @(posedge clk) !A1 |-> X
    );

// When A1 is high and B1_N is high, X must be high regardless of A2.
    check_a1_high_b1n_high_forces_high: assert property (
        @(posedge clk) (A1 && B1_N) |-> X
    );

// When A1 is high and A2 is low, X must be low.
    check_a1_high_a2_low_forces_low: assert property (
        @(posedge clk) (A1 && !A2) |-> !X
    );

// When A1 is low and B1_N is low, X must be low.
    check_a1_low_b1n_low_forces_low: assert property (
        @(posedge clk) (!A1 && !B1_N) |-> !X
    );

endmodule
