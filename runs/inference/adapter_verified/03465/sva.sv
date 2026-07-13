module sky130_fd_sc_hvl__a22o_sva (
    input logic clk,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic B2,
    input logic X
);

// X matches the implemented combinational equation.
    check_function_equivalence: assert property (
        @(posedge clk) X == ((A1 & A2 & ~B1 & ~B2) | (~A1 & ~A2 & B1 & B2))
    );

// When both A inputs are high and both B inputs are low, X must be high.
    check_a_high_b_low_sets_x: assert property (
        @(posedge clk) (A1 & A2 & ~B1 & ~B2) |-> X
    );

// When both A inputs are low and both B inputs are high, X must be high.
    check_a_low_b_high_sets_x: assert property (
        @(posedge clk) (~A1 & ~A2 & B1 & B2) |-> X
    );

// Any mismatch between A and B inputs forces X low.
    check_mismatch_clears_x: assert property (
        @(posedge clk) ((A1 == B1) || (A2 == B2)) |-> !X
    );

// X high implies the implemented input pattern is present.
    check_x_high_has_valid_cause: assert property (
        @(posedge clk) X |-> ((A1 & A2 & ~B1 & ~B2) | (~A1 & ~A2 & B1 & B2))
    );

endmodule
