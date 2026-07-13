module sky130_fd_sc_hd__or2b_sva (
    input logic X,
    input logic A,
    input logic B_N
);
    // Combinational gate (X = A | ~B_N); no clock or reset in DUT; sample on A/B_N edges.

    // X must equal A | ~B_N whenever inputs toggle.
    check_func_equivalence_on_edges: assert property (
        @(posedge A or posedge B_N or negedge B_N) X == (A | ~B_N)
    );

    // A high forces X high.
    check_A_high_forces_X_high: assert property (
        @(posedge A) X == 1'b1
    );

    // B_N low forces X high.
    check_BN_low_forces_X_high: assert property (
        @(negedge B_N) X == 1'b1
    );

    // If A is 0 and B_N is 1, X must be 0.
    check_zero_condition: assert property (
        @(posedge A or posedge B_N or negedge B_N) ((A == 1'b0) && (B_N == 1'b1)) |-> (X == 1'b0)
    );

    // If X is 0, then A must be 0 and B_N must be 1.
    check_x_zero_implies_inputs: assert property (
        @(posedge A or posedge B_N or negedge B_N) (X == 1'b0) |-> ((A == 1'b0) && (B_N == 1'b1))
    );

    // If B_N is 0, X must be 1 regardless of A.
    check_BN_zero_implies_X_one: assert property (
        @(posedge A or posedge B_N or negedge B_N) (B_N == 1'b0) |-> (X == 1'b1)
    );

    // If X is 1, then A is 1 or B_N is 0.
    check_x_one_implies_inputs: assert property (
        @(posedge A or posedge B_N or negedge B_N) (X == 1'b1) |-> ((A == 1'b1) || (B_N == 1'b0))
    );
endmodule