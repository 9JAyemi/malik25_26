module xnor2_sva (
    input logic Y,
    input logic A,
    input logic B,
    input logic VPWR,
    input logic VGND,
    input logic VPB,
    input logic VNB,
    input logic A_inv,
    input logic B_inv,
    input logic A_B,
    input logic A_inv_B_inv
);
    // Y equals XNOR of A and B (functional definition).
    check_y_eq_xnor: assert property (
        @(posedge A or negedge A or posedge B or negedge B) ##0 (Y == (A ^~ B))
    );

    // A_inv is the inversion of A.
    check_a_inv_is_not_a: assert property (
        @(posedge A or negedge A) ##0 (A_inv == ~A)
    );

    // B_inv is the inversion of B.
    check_b_inv_is_not_b: assert property (
        @(posedge B or negedge B) ##0 (B_inv == ~B)
    );

    // A_B is the AND of A and B.
    check_a_b_and: assert property (
        @(posedge A or negedge A or posedge B or negedge B) ##0 (A_B == (A & B))
    );

    // A_inv_B_inv is the AND of A_inv and B_inv.
    check_a_inv_b_inv_and: assert property (
        @(posedge A_inv or negedge A_inv or posedge B_inv or negedge B_inv or posedge A or negedge A or posedge B or negedge B) ##0
        (A_inv_B_inv == (A_inv & B_inv))
    );

    // A_inv_B_inv equals (~A & ~B).
    check_a_inv_b_inv_matches_inverts: assert property (
        @(posedge A or negedge A or posedge B or negedge B) ##0 (A_inv_B_inv == (~A & ~B))
    );

    // Y is the OR of the two AND terms.
    check_y_or_of_terms: assert property (
        @(posedge A_B or negedge A_B or posedge A_inv_B_inv or negedge A_inv_B_inv or posedge A or negedge A or posedge B or negedge B or posedge Y or negedge Y) ##0
        (Y == (A_B | A_inv_B_inv))
    );

    // When Y rises, inputs must be equal.
    check_y_rise_inputs_equal: assert property (
        @(posedge Y) ##0 (A == B)
    );

    // When Y falls, inputs must be different.
    check_y_fall_inputs_different: assert property (
        @(negedge Y) ##0 (A != B)
    );

    // B_inv does not change when only A toggles and B is stable.
    check_b_inv_independent_of_a: assert property (
        @(posedge A or negedge A) $stable(B) |-> ##0 $stable(B_inv)
    );

    // A_inv does not change when only B toggles and A is stable.
    check_a_inv_independent_of_b: assert property (
        @(posedge B or negedge B) $stable(A) |-> ##0 $stable(A_inv)
    );
endmodule