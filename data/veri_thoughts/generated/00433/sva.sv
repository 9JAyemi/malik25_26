module sky130_fd_sc_ms__or4bb_sva (
    input logic clk,
    input logic X,
    input logic A,
    input logic B,
    input logic C_N,
    input logic D_N
);

    // X matches the OR of A, B, and the NAND of C_N and D_N.
    check_functional_equivalence: assert property (
        @(posedge clk) X == (A | B | ~(C_N & D_N))
    );

    // A high forces X high.
    check_a_forces_x_high: assert property (
        @(posedge clk) A |-> (X == 1'b1)
    );

    // B high forces X high.
    check_b_forces_x_high: assert property (
        @(posedge clk) B |-> (X == 1'b1)
    );

    // C_N low forces X high through the NAND term.
    check_c_n_low_forces_x_high: assert property (
        @(posedge clk) !C_N |-> (X == 1'b1)
    );

    // D_N low forces X high through the NAND term.
    check_d_n_low_forces_x_high: assert property (
        @(posedge clk) !D_N |-> (X == 1'b1)
    );

    // X can be low only when A and B are low and both NAND inputs are high.
    check_x_low_only_in_all_inactive_case: assert property (
        @(posedge clk) !X |-> (!A && !B && C_N && D_N)
    );

    // With A and B low, X reduces to the NAND of C_N and D_N.
    check_ab_low_reduces_to_nand: assert property (
        @(posedge clk) (!A && !B) |-> (X == ~(C_N & D_N))
    );

endmodule