module sky130_fd_sc_hdll__or4bb_sva (
    input logic clk,
    input logic X,
    input logic A,
    input logic B,
    input logic C_N,
    input logic D_N
);

    // X implements A OR B OR the NAND of C_N and D_N.
    check_function_equation: assert property (
        @(posedge clk) X == (A | B | ~(C_N & D_N))
    );

    // A being high forces X high.
    check_a_forces_high: assert property (
        @(posedge clk) A |-> X
    );

    // B being high forces X high.
    check_b_forces_high: assert property (
        @(posedge clk) B |-> X
    );

    // C_N being low forces X high through the NAND term.
    check_c_n_low_forces_high: assert property (
        @(posedge clk) !C_N |-> X
    );

    // D_N being low forces X high through the NAND term.
    check_d_n_low_forces_high: assert property (
        @(posedge clk) !D_N |-> X
    );

    // X is low only in the all-inactive input case.
    check_all_inactive_drives_low: assert property (
        @(posedge clk) (!A && !B && C_N && D_N) |-> !X
    );

endmodule