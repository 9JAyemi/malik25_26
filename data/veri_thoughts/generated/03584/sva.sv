module sky130_fd_sc_lp__nand4b_sva (
    input logic clk,
    input logic Y,
    input logic A_N,
    input logic B,
    input logic C,
    input logic D
);

    // Y implements the RTL gate function.
    check_function_implemented: assert property (
        @(posedge clk) Y == ~(D & C & B & ~A_N)
    );

    // All active inputs drive the NAND output low.
    check_all_active_inputs_drive_low: assert property (
        @(posedge clk) (!A_N && B && C && D) |-> !Y
    );

    // A low output only occurs for the active input combination.
    check_low_output_only_when_all_active: assert property (
        @(posedge clk) !Y |-> (!A_N && B && C && D)
    );

    // With B, C, and D high, Y follows A_N.
    check_a_n_controls_output_when_bcd_high: assert property (
        @(posedge clk) (B && C && D) |-> (Y == A_N)
    );

    // With A_N low and C/D high, Y is the inverse of B.
    check_b_controls_output_when_a_ncd_active: assert property (
        @(posedge clk) (!A_N && C && D) |-> (Y == !B)
    );

    // With A_N low and B/D high, Y is the inverse of C.
    check_c_controls_output_when_a_nbd_active: assert property (
        @(posedge clk) (!A_N && B && D) |-> (Y == !C)
    );

    // With A_N low and B/C high, Y is the inverse of D.
    check_d_controls_output_when_a_nbc_active: assert property (
        @(posedge clk) (!A_N && B && C) |-> (Y == !D)
    );

    // A high output means at least one input is in its inactive state.
    check_high_output_has_valid_cause: assert property (
        @(posedge clk) Y |-> (A_N || !B || !C || !D)
    );

endmodule