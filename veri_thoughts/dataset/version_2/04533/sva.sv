module sky130_fd_sc_hd__or4bb_sva (
    input logic clk,
    input logic X,
    input logic A,
    input logic B,
    input logic C_N,
    input logic D_N
);

    // No RTL clock or reset; clk is the sampling clock for this combinational cell.

    // X matches the implemented OR of A, B, and NAND(C_N, D_N).
    check_x_function: assert property (
        @(posedge clk) X == (A | B | ~(C_N & D_N))
    );

    // A high forces X high.
    check_a_forces_x_high: assert property (
        @(posedge clk) A |-> X
    );

    // B high forces X high.
    check_b_forces_x_high: assert property (
        @(posedge clk) B |-> X
    );

    // C_N low forces X high through the NAND term.
    check_cn_low_forces_x_high: assert property (
        @(posedge clk) !C_N |-> X
    );

    // D_N low forces X high through the NAND term.
    check_dn_low_forces_x_high: assert property (
        @(posedge clk) !D_N |-> X
    );

    // With A and B low, X is determined only by the NAND term.
    check_nand_term_when_a_b_low: assert property (
        @(posedge clk) (!A && !B) |-> (X == ~(C_N & D_N))
    );

    // With C_N and D_N high, X is determined only by A or B.
    check_or_term_when_nand_inactive: assert property (
        @(posedge clk) (C_N && D_N) |-> (X == (A | B))
    );

    // When all effective OR inputs are low, X is low.
    check_all_terms_low_drive_x_low: assert property (
        @(posedge clk) (!A && !B && C_N && D_N) |-> !X
    );

    // If X is low, all effective OR inputs must be low.
    check_x_low_requires_all_terms_low: assert property (
        @(posedge clk) !X |-> (!A && !B && C_N && D_N)
    );

endmodule