module sky130_fd_sc_hd__or2b_sva (
    input logic X,
    input logic A,
    input logic B_N,
    input logic VPWR,
    input logic VGND
);
    // No clock/reset in RTL; pure combinational: X = A | ~B_N; sample on VPWR posedge.

    // If A is 1, X must be 1.
    check_A1_implies_X1: assert property (
        @(posedge VPWR) (A == 1'b1) |-> (X == 1'b1)
    );

    // If B_N is 0, X must be 1.
    check_BN0_implies_X1: assert property (
        @(posedge VPWR) (B_N == 1'b0) |-> (X == 1'b1)
    );

    // If A is 0 and B_N is 1, X must be 0.
    check_only_zero_case: assert property (
        @(posedge VPWR) ((A == 1'b0) && (B_N == 1'b1)) |-> (X == 1'b0)
    );

    // If X is 0, then A must be 0 and B_N must be 1.
    check_X0_implies_inputs: assert property (
        @(posedge VPWR) (X == 1'b0) |-> ((A == 1'b0) && (B_N == 1'b1))
    );

    // If X is 1, then A is 1 or B_N is 0.
    check_X1_implies_inputs: assert property (
        @(posedge VPWR) (X == 1'b1) |-> ((A == 1'b1) || (B_N == 1'b0))
    );

    // Truth table: A=0, B_N=0 -> X=1.
    check_truth_00: assert property (
        @(posedge VPWR) ((A == 1'b0) && (B_N == 1'b0)) |-> (X == 1'b1)
    );

    // Truth table: A=0, B_N=1 -> X=0.
    check_truth_01: assert property (
        @(posedge VPWR) ((A == 1'b0) && (B_N == 1'b1)) |-> (X == 1'b0)
    );

    // Truth table: A=1, B_N=0 -> X=1.
    check_truth_10: assert property (
        @(posedge VPWR) ((A == 1'b1) && (B_N == 1'b0)) |-> (X == 1'b1)
    );

    // Truth table: A=1, B_N=1 -> X=1.
    check_truth_11: assert property (
        @(posedge VPWR) ((A == 1'b1) && (B_N == 1'b1)) |-> (X == 1'b1)
    );

    // When B_N is 1, X equals A.
    check_BN1_X_eq_A: assert property (
        @(posedge VPWR) (B_N == 1'b1) |-> (X == A)
    );

    // When A is 0, X equals !B_N.
    check_A0_X_eq_notBN: assert property (
        @(posedge VPWR) (A == 1'b0) |-> (X == !B_N)
    );

    // If A and B_N are stable between samples, X must be stable.
    check_stability_with_stable_inputs: assert property (
        @(posedge VPWR) ($stable(A) && $stable(B_N)) |-> $stable(X)
    );

endmodule