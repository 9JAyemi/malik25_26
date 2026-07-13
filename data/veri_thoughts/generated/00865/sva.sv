module xor3_1_sva (
    input logic X,
    input logic A,
    input logic B,
    input logic C
);
    // X equals A ^ B ^ C when sampled on A rising edge.
    check_xor_eq_on_A: assert property (
        @(posedge A) X == (A ^ B ^ C)
    );

    // X equals A ^ B ^ C when sampled on B rising edge.
    check_xor_eq_on_B: assert property (
        @(posedge B) X == (A ^ B ^ C)
    );

    // X equals A ^ B ^ C when sampled on C rising edge.
    check_xor_eq_on_C: assert property (
        @(posedge C) X == (A ^ B ^ C)
    );

    // With B=0 and C=0, X follows A.
    check_B0_C0_eq_A: assert property (
        @(posedge A) (B == 1'b0 && C == 1'b0) |-> (X == A)
    );

    // With B=1 and C=1, X follows A.
    check_B1_C1_eq_A: assert property (
        @(posedge A) (B == 1'b1 && C == 1'b1) |-> (X == A)
    );

    // With B=1 and C=0, X equals bitwise NOT of A.
    check_B1_C0_eq_notA: assert property (
        @(posedge B) (B == 1'b1 && C == 1'b0) |-> (X == ~A)
    );

    // With B=0 and C=1, X equals bitwise NOT of A.
    check_B0_C1_eq_notA: assert property (
        @(posedge C) (B == 1'b0 && C == 1'b1) |-> (X == ~A)
    );

    // If A equals B, then X equals C.
    check_AeqB_implies_XeqC: assert property (
        @(posedge A) (A == B) |-> (X == C)
    );

    // If B equals C, then X equals A.
    check_BeqC_implies_XeqA: assert property (
        @(posedge B) (B == C) |-> (X == A)
    );

    // If A equals C, then X equals B.
    check_AeqC_implies_XeqB: assert property (
        @(posedge C) (A == C) |-> (X == B)
    );
endmodule