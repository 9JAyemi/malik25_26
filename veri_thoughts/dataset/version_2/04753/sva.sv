module sky130_fd_sc_hdll__nand4b_sva (
    input logic clk,
    input logic Y,
    input logic A_N,
    input logic B,
    input logic C,
    input logic D
);

    // Y matches the implemented NAND-with-inverted-A function.
    check_function: assert property (
        @(posedge clk) Y == (A_N || !B || !C || !D)
    );

    // A_N high forces the inverted NAND input low, so Y must be high.
    check_a_n_high_forces_y_high: assert property (
        @(posedge clk) A_N |-> Y
    );

    // A_N low with B, C, and D high drives the NAND output low.
    check_all_active_inputs_drive_y_low: assert property (
        @(posedge clk) (!A_N && B && C && D) |-> !Y
    );

    // B low prevents the NAND pull-down condition and keeps Y high.
    check_b_low_forces_y_high: assert property (
        @(posedge clk) !B |-> Y
    );

    // C low prevents the NAND pull-down condition and keeps Y high.
    check_c_low_forces_y_high: assert property (
        @(posedge clk) !C |-> Y
    );

    // D low prevents the NAND pull-down condition and keeps Y high.
    check_d_low_forces_y_high: assert property (
        @(posedge clk) !D |-> Y
    );

    // Y low can occur only for A_N low with B, C, and D high.
    check_y_low_only_on_active_combination: assert property (
        @(posedge clk) !Y |-> (!A_N && B && C && D)
    );

endmodule