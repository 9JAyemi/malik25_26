module my_module_sva (
    input logic clk,
    input logic A1,
    input logic A2,
    input logic A3,
    input logic B1,
    input logic B2,
    input logic X
);

// X must match the RTL combinational equation.
    check_functional_equivalence: assert property (
        @(posedge clk) X == ((A1 | (A2 & ~A3)) & B1)
    );

// A1 high with B1 high must drive X high.
    check_a1_path: assert property (
        @(posedge clk) (A1 && B1) |-> X
    );

// A2 high and A3 low with B1 high must drive X high.
    check_a2_a3_path: assert property (
        @(posedge clk) (A2 && !A3 && B1) |-> X
    );

// B1 low must force X low.
    check_b1_low_forces_x_low: assert property (
        @(posedge clk) !B1 |-> !X
    );

// A1 low with B1 high must force X low.
    check_a1_low_forces_x_low: assert property (
        @(posedge clk) (!A1 && B1) |-> !X
    );

// A2 low with B1 high must force X low.
    check_a2_low_forces_x_low: assert property (
        @(posedge clk) (!A2 && B1) |-> !X
    );

// A3 high with B1 high must force X low.
    check_a3_high_forces_x_low: assert property (
        @(posedge clk) (A3 && B1) |-> !X
    );

endmodule
