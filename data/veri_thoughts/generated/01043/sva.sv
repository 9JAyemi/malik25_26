module sky130_fd_sc_lp__o22a_sva (
    input logic CLK,
    input logic X,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic B2
);
    ///// Functional equivalence /////
    // X implements (A1|A2) & (B1|B2).
    check_function_equivalence: assert property (
        @(posedge CLK) X === ((A1 | A2) & (B1 | B2))
    );

    ///// Necessary conditions for X HIGH /////
    // If X is HIGH, at least one of A1/A2 is HIGH.
    check_X_requires_A_group: assert property (
        @(posedge CLK) X |-> (A1 | A2)
    );
    // If X is HIGH, at least one of B1/B2 is HIGH.
    check_X_requires_B_group: assert property (
        @(posedge CLK) X |-> (B1 | B2)
    );

    ///// Forcing LOW conditions /////
    // If both A1 and A2 are LOW, X must be LOW.
    check_A_group_zero_forces_X_zero: assert property (
        @(posedge CLK) (~A1 & ~A2) |-> (X == 1'b0)
    );
    // If both B1 and B2 are LOW, X must be LOW.
    check_B_group_zero_forces_X_zero: assert property (
        @(posedge CLK) (~B1 & ~B2) |-> (X == 1'b0)
    );

    ///// Sufficient conditions for X HIGH /////
    // If A1 and B1 are HIGH, X must be HIGH.
    check_pair_A1B1_high_sets_X: assert property (
        @(posedge CLK) (A1 & B1) |-> (X == 1'b1)
    );
    // If A1 and B2 are HIGH, X must be HIGH.
    check_pair_A1B2_high_sets_X: assert property (
        @(posedge CLK) (A1 & B2) |-> (X == 1'b1)
    );
    // If A2 and B1 are HIGH, X must be HIGH.
    check_pair_A2B1_high_sets_X: assert property (
        @(posedge CLK) (A2 & B1) |-> (X == 1'b1)
    );
    // If A2 and B2 are HIGH, X must be HIGH.
    check_pair_A2B2_high_sets_X: assert property (
        @(posedge CLK) (A2 & B2) |-> (X == 1'b1)
    );

    ///// Equivalence (other direction) /////
    // If (A1|A2)&(B1|B2) is HIGH, X must be HIGH.
    check_expr_implies_X: assert property (
        @(posedge CLK) (((A1 | A2) & (B1 | B2)) == 1'b1) |-> (X == 1'b1)
    );
endmodule