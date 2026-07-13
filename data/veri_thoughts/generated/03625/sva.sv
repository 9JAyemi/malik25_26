module sky130_fd_sc_lp__nand4bb_sva (
    input logic clk,
    input logic Y,
    input logic A_N,
    input logic B_N,
    input logic C,
    input logic D
);

    // Y matches the OR of A_N, B_N, and the NAND of C and D.
    check_output_equation: assert property (
        @(posedge clk) Y == (A_N | B_N | ~(C & D))
    );

    // A_N high directly forces Y high.
    check_a_n_high_forces_y_high: assert property (
        @(posedge clk) A_N |-> Y
    );

    // B_N high directly forces Y high.
    check_b_n_high_forces_y_high: assert property (
        @(posedge clk) B_N |-> Y
    );

    // C low makes the internal NAND term high, forcing Y high.
    check_c_low_forces_y_high: assert property (
        @(posedge clk) !C |-> Y
    );

    // D low makes the internal NAND term high, forcing Y high.
    check_d_low_forces_y_high: assert property (
        @(posedge clk) !D |-> Y
    );

    // When all effective inputs are active, Y must be low.
    check_all_active_drives_y_low: assert property (
        @(posedge clk) (!A_N && !B_N && C && D) |-> !Y
    );

    // Y can be low only for the single active-low minterm.
    check_y_low_only_under_active_minterm: assert property (
        @(posedge clk) !Y |-> (!A_N && !B_N && C && D)
    );

endmodule