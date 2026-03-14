module sky130_fd_sc_hd__maj3_sva (
    input logic X,
    input logic A,
    input logic B,
    input logic C
);

    ///// Majority function /////
    // X equals the majority-of-three of A, B, C.
    check_majority_equivalence: assert property (
        @(posedge $global_clock) disable iff (1'b0) X == ((A & B) | (A & C) | (B & C))
    );

    ///// Dominance when two inputs match /////
    // If A equals B, X must equal A.
    check_equal_ab_dominates: assert property (
        @(posedge $global_clock) disable iff (1'b0) (A == B) |-> (X == A)
    );
    // If A equals C, X must equal A.
    check_equal_ac_dominates: assert property (
        @(posedge $global_clock) disable iff (1'b0) (A == C) |-> (X == A)
    );
    // If B equals C, X must equal B.
    check_equal_bc_dominates: assert property (
        @(posedge $global_clock) disable iff (1'b0) (B == C) |-> (X == B)
    );

    ///// At least two inputs HIGH implies X HIGH /////
    // If A and B are 1, X must be 1 (independent of C).
    check_two_high_ab_implies_x: assert property (
        @(posedge $global_clock) disable iff (1'b0) (A && B) |-> (X == 1'b1)
    );
    // If A and C are 1, X must be 1 (independent of B).
    check_two_high_ac_implies_x: assert property (
        @(posedge $global_clock) disable iff (1'b0) (A && C) |-> (X == 1'b1)
    );
    // If B and C are 1, X must be 1 (independent of A).
    check_two_high_bc_implies_x: assert property (
        @(posedge $global_clock) disable iff (1'b0) (B && C) |-> (X == 1'b1)
    );

    ///// At least two inputs LOW implies X LOW /////
    // If A and B are 0, X must be 0 (independent of C).
    check_two_low_ab_implies_nx: assert property (
        @(posedge $global_clock) disable iff (1'b0) (!A && !B) |-> (X == 1'b0)
    );
    // If A and C are 0, X must be 0 (independent of B).
    check_two_low_ac_implies_nx: assert property (
        @(posedge $global_clock) disable iff (1'b0) (!A && !C) |-> (X == 1'b0)
    );
    // If B and C are 0, X must be 0 (independent of A).
    check_two_low_bc_implies_nx: assert property (
        @(posedge $global_clock) disable iff (1'b0) (!B && !C) |-> (X == 1'b0)
    );

endmodule