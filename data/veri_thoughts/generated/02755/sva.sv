module and_gate_sva (
    input logic A,
    input logic B,
    input logic C,
    input logic Y
);
    // No clock/reset in RTL; pure combinational AND. Assertions sample on input posedges.

    // Y must equal A & B & C sampled on posedge A.
    check_y_matches_and_on_A: assert property (
        @(posedge A) Y == (A & B & C)
    );

    // Y must equal A & B & C sampled on posedge B.
    check_y_matches_and_on_B: assert property (
        @(posedge B) Y == (A & B & C)
    );

    // Y must equal A & B & C sampled on posedge C.
    check_y_matches_and_on_C: assert property (
        @(posedge C) Y == (A & B & C)
    );

    // When B and C are HIGH, Y follows A on posedge A.
    check_follow_A_when_BC_high: assert property (
        @(posedge A) (B && C) |-> (Y == A)
    );

    // When A and C are HIGH, Y follows B on posedge B.
    check_follow_B_when_AC_high: assert property (
        @(posedge B) (A && C) |-> (Y == B)
    );

    // When A and B are HIGH, Y follows C on posedge C.
    check_follow_C_when_AB_high: assert property (
        @(posedge C) (A && B) |-> (Y == C)
    );

    // If B is LOW, Y must be LOW on posedge A.
    check_y_zero_when_B_zero_on_A: assert property (
        @(posedge A) (!B) |-> (Y == 1'b0)
    );

    // If C is LOW, Y must be LOW on posedge A.
    check_y_zero_when_C_zero_on_A: assert property (
        @(posedge A) (!C) |-> (Y == 1'b0)
    );

    // If Y is HIGH on posedge B, A and C must be HIGH.
    check_y_high_implies_A_and_C_high_on_B: assert property (
        @(posedge B) Y |-> (A && C)
    );

    // If Y is HIGH on posedge C, A and B must be HIGH.
    check_y_high_implies_A_and_B_high_on_C: assert property (
        @(posedge C) Y |-> (A && B)
    );
endmodule