module xnor3_sva (
    input logic A,
    input logic B,
    input logic C,
    input logic X,
    input logic VPB,
    input logic VPWR,
    input logic VGND,
    input logic VNB
);
    // No clock/reset in RTL; combinational logic; sample on any input edge.

    // X equals the inversion of the OR of all input pairs.
    check_function_equivalence: assert property (
        @(posedge A or posedge B or posedge C or negedge A or negedge B or negedge C)
        X == ~((A & B) | (A & C) | (B & C))
    );

    // If X is 0, at least one input pair must be 1.
    check_x0_implies_some_pair_high: assert property (
        @(posedge A or posedge B or posedge C or negedge A or negedge B or negedge C)
        (X == 1'b0) |-> ((A & B) | (A & C) | (B & C))
    );

    // If X is 1, no input pair can be 1.
    check_x1_implies_no_pair_high: assert property (
        @(posedge A or posedge B or posedge C or negedge A or negedge B or negedge C)
        (X == 1'b1) |-> ~((A & B) | (A & C) | (B & C))
    );

    // When all inputs are 0, X must be 1.
    check_all_zero_x_is_one: assert property (
        @(posedge A or posedge B or posedge C or negedge A or negedge B or negedge C)
        (~A & ~B & ~C) |-> (X == 1'b1)
    );

    // When only A is 1, X must be 1.
    check_onehot_a_x_is_one: assert property (
        @(posedge A or posedge B or posedge C or negedge A or negedge B or negedge C)
        (A & ~B & ~C) |-> (X == 1'b1)
    );

    // When only B is 1, X must be 1.
    check_onehot_b_x_is_one: assert property (
        @(posedge A or posedge B or posedge C or negedge A or negedge B or negedge C)
        (~A & B & ~C) |-> (X == 1'b1)
    );

    // When only C is 1, X must be 1.
    check_onehot_c_x_is_one: assert property (
        @(posedge A or posedge B or posedge C or negedge A or negedge B or negedge C)
        (~A & ~B & C) |-> (X == 1'b1)
    );

    // When all inputs are 1, X must be 0.
    check_all_one_x_is_zero: assert property (
        @(posedge A or posedge B or posedge C or negedge A or negedge B or negedge C)
        (A & B & C) |-> (X == 1'b0)
    );

    // If A and B are both 1 (at least two highs), X must be 0.
    check_ab_pair_implies_x_zero: assert property (
        @(posedge A or posedge B or posedge C or negedge A or negedge B or negedge C)
        (A & B) |-> (X == 1'b0)
    );

    // If A and C are both 1 (at least two highs), X must be 0.
    check_ac_pair_implies_x_zero: assert property (
        @(posedge A or posedge B or posedge C or negedge A or negedge B or negedge C)
        (A & C) |-> (X == 1'b0)
    );

endmodule