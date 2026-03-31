module sky130_fd_sc_ls__o21a_sva (
    input logic clk,
    input logic X,
    input logic A1,
    input logic A2,
    input logic B1
);

// X must match the implemented O21A function.
    check_functional_equivalence: assert property (
        @(posedge clk) X == (A1 | A2) & B1
    );

// B1 low forces X low.
    check_b1_low_forces_x_low: assert property (
        @(posedge clk) !B1 |-> !X
    );

// A1 high with B1 high drives X high.
    check_a1_high_with_b1_high_drives_x_high: assert property (
        @(posedge clk) (A1 && B1) |-> X
    );

// A2 high with B1 high drives X high.
    check_a2_high_with_b1_high_drives_x_high: assert property (
        @(posedge clk) (A2 && B1) |-> X
    );

// X high requires B1 to be high.
    check_x_high_requires_b1_high: assert property (
        @(posedge clk) X |-> B1
    );

// X high requires at least one A input to be high.
    check_x_high_requires_a_input_high: assert property (
        @(posedge clk) X |-> (A1 || A2)
    );

endmodule
