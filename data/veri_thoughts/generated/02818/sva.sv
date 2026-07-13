module sky130_fd_sc_ls__or4bb_sva (
    input logic X,
    input logic A,
    input logic B,
    input logic C_N,
    input logic D_N
);
    // X implements A | B | ~C_N | ~D_N sampled on A rising edge.
    check_truth_on_A_posedge: assert property (
        @(posedge A) X == (A | B | ~C_N | ~D_N)
    );

    // X implements A | B | ~C_N | ~D_N sampled on B rising edge.
    check_truth_on_B_posedge: assert property (
        @(posedge B) X == (A | B | ~C_N | ~D_N)
    );

    // X implements A | B | ~C_N | ~D_N sampled on C_N rising edge.
    check_truth_on_Cn_posedge: assert property (
        @(posedge C_N) X == (A | B | ~C_N | ~D_N)
    );

    // X implements A | B | ~C_N | ~D_N sampled on D_N rising edge.
    check_truth_on_Dn_posedge: assert property (
        @(posedge D_N) X == (A | B | ~C_N | ~D_N)
    );

    // X implements A | B | ~C_N | ~D_N sampled on X rising edge.
    check_truth_on_X_posedge: assert property (
        @(posedge X) X == (A | B | ~C_N | ~D_N)
    );

    // Asserting C_N low forces X high.
    check_Cn_low_forces_X_high: assert property (
        @(negedge C_N) X == 1'b1
    );

    // Asserting D_N low forces X high.
    check_Dn_low_forces_X_high: assert property (
        @(negedge D_N) X == 1'b1
    );

    // With C_N just risen and D_N already high, X reduces to A | B.
    check_reduce_to_AorB_on_Cn_rise: assert property (
        @(posedge C_N) (D_N == 1'b1) |-> (X == (A | B))
    );

    // With D_N just risen and C_N already high, X reduces to A | B.
    check_reduce_to_AorB_on_Dn_rise: assert property (
        @(posedge D_N) (C_N == 1'b1) |-> (X == (A | B))
    );

    // When X falls low, all inputs must make all OR terms false.
    check_X_low_implies_all_inactive: assert property (
        @(negedge X) (A == 1'b0) && (B == 1'b0) && (C_N == 1'b1) && (D_N == 1'b1)
    );
endmodule