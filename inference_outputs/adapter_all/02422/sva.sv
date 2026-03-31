module sky130_fd_sc_hdll__nand4bb_sva (
    input logic clk,
    input logic Y,
    input logic A_N,
    input logic B_N,
    input logic C,
    input logic D
);

    // Y matches the implemented NAND/OR/BUF function.
    check_functional_equivalence: assert property (
        @(posedge clk) Y == (B_N | A_N | ~(C & D))
    );

    // A_N high forces the OR output high.
    check_a_n_high_forces_y_high: assert property (
        @(posedge clk) A_N |-> Y
    );

    // B_N high forces the OR output high.
    check_b_n_high_forces_y_high: assert property (
        @(posedge clk) B_N |-> Y
    );

    // C low forces the NAND output low, so Y must be high.
    check_c_low_forces_y_high: assert property (
        @(posedge clk) !C |-> Y
    );

    // D low forces the NAND output low, so Y must be high.
    check_d_low_forces_y_high: assert property (
        @(posedge clk) !D |-> Y
    );

    // With all active terms low, Y must be low.
    check_all_active_terms_low_forces_y_low: assert property (
        @(posedge clk) (!A_N && !B_N && C && D) |-> !Y
    );

    // With all active terms low, Y must be low.
    check_all_active_terms_low_forces_y_low: assert property (
        @(posedge clk) (!A_N && !B_N && C && D) |-> !Y
    );

    // With A_N and B_N low, Y reduces to the NAND of C and D.
    check_a_n_b_n_low_reduces_to_nand: assert property (
        @(posedge clk) (!A_N && !B_N) |-> (Y == ~(C & D))
    );

    // With C and D high, Y reduces to the OR of A_N and B_N.
    check_c_d_high_reduces_to_or: assert property (
        @(posedge clk) (C && D) |-> (Y == (A_N | B_N))
    );

endmodule