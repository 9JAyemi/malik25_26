module sky130_fd_sc_hd__o211a_sva (
    input logic clk,
    input logic X,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic C1
);

// X matches the implemented OR-AND function.
    check_functional_equivalence: assert property (
        @(posedge clk) X == ((A1 | A2) & B1 & C1)
    );

// B1 low forces X low.
    check_b1_low_forces_x_low: assert property (
        @(posedge clk) !B1 |-> !X
    );

// C1 low forces X low.
    check_c1_low_forces_x_low: assert property (
        @(posedge clk) !C1 |-> !X
    );

// A1 high with B1 and C1 high drives X high.
    check_a1_high_drives_x_high: assert property (
        @(posedge clk) (A1 && B1 && C1) |-> X
    );

// A2 high with B1 and C1 high drives X high.
    check_a2_high_drives_x_high: assert property (
        @(posedge clk) (A2 && B1 && C1) |-> X
    );

// X high requires B1, C1, and at least one of A1/A2 to be high.
    check_x_high_requires_all_inputs: assert property (
        @(posedge clk) X |-> (B1 && C1 && (A1 || A2))
    );

endmodule
