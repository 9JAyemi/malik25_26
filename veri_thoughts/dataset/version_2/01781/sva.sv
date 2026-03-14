module multi_gate_module_sva (
    input logic A,
    input logic B,
    input logic C,
    input logic D,
    input logic E,
    input logic Y
);
    // No clock/reset in RTL; sample on any input rising edge.

    // Y equals (A & B) | (C & D) | (E & (A ^ B)).
    check_y_equals_spec: assert property (
        @(posedge A or posedge B or posedge C or posedge D or posedge E)
        Y == ((A & B) | (C & D) | (E & (A ^ B)))
    );

    // If A and B are both 1, Y must be 1.
    check_ab_implies_y: assert property (
        @(posedge A or posedge B or posedge C or posedge D or posedge E)
        (A & B) |-> Y
    );

    // If C and D are both 1, Y must be 1.
    check_cd_implies_y: assert property (
        @(posedge A or posedge B or posedge C or posedge D or posedge E)
        (C & D) |-> Y
    );

    // If E is 1 and A^B is 1, Y must be 1.
    check_exor_implies_y: assert property (
        @(posedge A or posedge B or posedge C or posedge D or posedge E)
        (E & (A ^ B)) |-> Y
    );

    // If Y is 0, all three terms must be 0.
    check_y_zero_implies_terms_zero: assert property (
        @(posedge A or posedge B or posedge C or posedge D or posedge E)
        (Y == 1'b0) |-> ~((A & B) | (C & D) | (E & (A ^ B)))
    );

    // When E is 0, Y reduces to (A & B) | (C & D).
    check_e_zero_reduction: assert property (
        @(posedge A or posedge B or posedge C or posedge D or posedge E)
        (E == 1'b0) |-> (Y == ((A & B) | (C & D)))
    );

    // When A equals B, Y reduces to (A & B) | (C & D) (since A^B==0).
    check_a_eq_b_reduction: assert property (
        @(posedge A or posedge B or posedge C or posedge D or posedge E)
        (A == B) |-> (Y == ((A & B) | (C & D)))
    );

    // If Y is 1 and neither (A & B) nor (E & (A ^ B)) is 1, then (C & D) must be 1.
    check_y_source_cd_when_others_off: assert property (
        @(posedge A or posedge B or posedge C or posedge D or posedge E)
        (Y && ~((A & B)) && ~((E & (A ^ B)))) |-> (C & D)
    );

    // If Y is 1 and neither (C & D) nor (E & (A ^ B)) is 1, then (A & B) must be 1.
    check_y_source_ab_when_others_off: assert property (
        @(posedge A or posedge B or posedge C or posedge D or posedge E)
        (Y && ~((C & D)) && ~((E & (A ^ B)))) |-> (A & B)
    );

    // If Y is 1 and neither (A & B) nor (C & D) is 1, then (E & (A ^ B)) must be 1.
    check_y_source_exor_when_others_off: assert property (
        @(posedge A or posedge B or posedge C or posedge D or posedge E)
        (Y && ~((A & B)) && ~((C & D))) |-> (E & (A ^ B))
    );
endmodule