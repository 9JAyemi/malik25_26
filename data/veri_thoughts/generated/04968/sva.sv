module sky130_fd_sc_lp__nand3b_sva (
    input logic clk,
    input logic Y,
    input logic A_N,
    input logic B,
    input logic C
);

    // Combinational DUT sampled on an external formal clock.

    // Y matches the implemented NOT-then-NAND function.
    check_output_function: assert property (
        @(posedge clk) (Y == ~(B & ~A_N & C))
    );

    // A_N high forces the inverted NAND input low, so Y must be high.
    check_a_n_high_forces_y_high: assert property (
        @(posedge clk) (A_N == 1'b1) |-> (Y == 1'b1)
    );

    // B low forces the NAND output high.
    check_b_low_forces_y_high: assert property (
        @(posedge clk) (B == 1'b0) |-> (Y == 1'b1)
    );

    // C low forces the NAND output high.
    check_c_low_forces_y_high: assert property (
        @(posedge clk) (C == 1'b0) |-> (Y == 1'b1)
    );

    // The only way Y can be low is with A_N low, B high, and C high.
    check_y_low_only_for_active_input_combo: assert property (
        @(posedge clk) (Y == 1'b0) |-> ((A_N == 1'b0) && (B == 1'b1) && (C == 1'b1))
    );

    // With A_N low and both B and C high, Y must be low.
    check_active_input_combo_drives_y_low: assert property (
        @(posedge clk) ((A_N == 1'b0) && (B == 1'b1) && (C == 1'b1)) |-> (Y == 1'b0)
    );

endmodule