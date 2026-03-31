module sky130_fd_sc_lp__o31a_sva (
    input logic clk,
    input logic X,
    input logic A1,
    input logic A2,
    input logic A3,
    input logic B1
);

// X matches the implemented OR-then-AND function.
    check_function_equivalence: assert property (
        @(posedge clk) X == (B1 & (A1 | A2 | A3))
    );

// B1 low forces X low.
    check_b1_low_forces_x_low: assert property (
        @(posedge clk) !B1 |-> !X
    );

// Any asserted A input with B1 high drives X high.
    check_any_a_with_b1_high_drives_x_high: assert property (
        @(posedge clk) (B1 & (A1 | A2 | A3)) |-> X
    );

// X high requires B1 to be high.
    check_x_high_requires_b1_high: assert property (
        @(posedge clk) X |-> B1
    );

// X high requires at least one A input to be high.
    check_x_high_requires_any_a_high: assert property (
        @(posedge clk) X |-> (A1 | A2 | A3)
    );

endmodule
