module my_xor3_sva (
    input logic A,
    input logic B,
    input logic C,
    input logic X
);

    // X equals A ^ B ^ C when sampled on A rising edge.
    check_x_equals_xor_on_A: assert property (
        @(posedge A) X == (A ^ B ^ C)
    );

    // X equals A ^ B ^ C when sampled on B rising edge.
    check_x_equals_xor_on_B: assert property (
        @(posedge B) X == (A ^ B ^ C)
    );

    // X equals A ^ B ^ C when sampled on C rising edge.
    check_x_equals_xor_on_C: assert property (
        @(posedge C) X == (A ^ B ^ C)
    );

    // If C is 0, output reduces to A ^ B.
    check_c_zero_reduces_to_ab: assert property (
        @(posedge C) (C == 1'b0) |-> (X == (A ^ B))
    );

    // If C is 1, output is inversion of A ^ B.
    check_c_one_inverts_ab: assert property (
        @(posedge C) (C == 1'b1) |-> (X == ~(A ^ B))
    );

    // Parity relation: X ^ C equals A ^ B.
    check_x_xor_c_equals_a_xor_b: assert property (
        @(posedge C) (X ^ C) == (A ^ B)
    );

    // If only A changes (B,C stable), X must toggle.
    check_toggle_on_A_only: assert property (
        @(posedge A) $stable(B) && $stable(C) |-> $changed(X)
    );

    // If only B changes (A,C stable), X must toggle.
    check_toggle_on_B_only: assert property (
        @(posedge B) $stable(A) && $stable(C) |-> $changed(X)
    );

    // If only C changes (A,B stable), X must toggle.
    check_toggle_on_C_only: assert property (
        @(posedge C) $stable(A) && $stable(B) |-> $changed(X)
    );

    // If A and B both change while C is stable, X holds.
    check_hold_on_A_and_B_change: assert property (
        @(posedge A) $changed(B) && $stable(C) |-> !$changed(X)
    );

    // If A and C both change while B is stable, X holds.
    check_hold_on_A_and_C_change: assert property (
        @(posedge A) $changed(C) && $stable(B) |-> !$changed(X)
    );

    // If A, B, and C all change together, X toggles.
    check_toggle_on_all_three_change: assert property (
        @(posedge A) $changed(B) && $changed(C) |-> $changed(X)
    );

    // If A equals B, X must equal C.
    check_when_AeqB_then_XeqC: assert property (
        @(posedge A) (A == B) |-> (X == C)
    );

    // If A equals C, X must equal B.
    check_when_AeqC_then_XeqB: assert property (
        @(posedge A) (A == C) |-> (X == B)
    );

    // If B equals C, X must equal A.
    check_when_BeqC_then_XeqA: assert property (
        @(posedge B) (B == C) |-> (X == A)
    );

endmodule