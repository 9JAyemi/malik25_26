module sky130_fd_sc_hdll__nand3b_sva (
    input logic clk,
    input logic Y,
    input logic A_N,
    input logic B,
    input logic C
);

    // Y must match the implemented NAND3B logic.
    check_nand3b_function: assert property (
        @(posedge clk) Y == ~(B & ~A_N & C)
    );

    // A_N high forces the output high.
    check_a_n_high_forces_y_high: assert property (
        @(posedge clk) (A_N == 1'b1) |-> (Y == 1'b1)
    );

    // B low forces the output high.
    check_b_low_forces_y_high: assert property (
        @(posedge clk) (B == 1'b0) |-> (Y == 1'b1)
    );

    // C low forces the output high.
    check_c_low_forces_y_high: assert property (
        @(posedge clk) (C == 1'b0) |-> (Y == 1'b1)
    );

    // The active input combination drives the output low.
    check_active_inputs_force_y_low: assert property (
        @(posedge clk) ((A_N == 1'b0) && (B == 1'b1) && (C == 1'b1)) |-> (Y == 1'b0)
    );

    // A low output can only occur for the active input combination.
    check_y_low_only_for_active_inputs: assert property (
        @(posedge clk) (Y == 1'b0) |-> ((A_N == 1'b0) && (B == 1'b1) && (C == 1'b1))
    );

endmodule