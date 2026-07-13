module and_or_not_sva (
    input logic CLK,
    input logic A,
    input logic B,
    input logic C,
    input logic Y
);
    // Y equals (A & B) OR (!C).
    check_functional_equivalence: assert property (
        @(posedge CLK) Y == ((A & B) | (!C))
    );

    // When C is LOW, Y must be HIGH.
    check_c_low_dominates: assert property (
        @(posedge CLK) (C == 1'b0) |-> (Y == 1'b1)
    );

    // When C is HIGH, Y equals A & B.
    check_c_high_matches_and: assert property (
        @(posedge CLK) (C == 1'b1) |-> (Y == (A & B))
    );

    // If Y is LOW, then C is HIGH and at least one of A or B is LOW.
    check_y_zero_implies_c_high_and_not_ab: assert property (
        @(posedge CLK) (Y == 1'b0) |-> (C == 1'b1) && ((A == 1'b0) || (B == 1'b0))
    );

    // If Y and C are HIGH, then both A and B are HIGH.
    check_y_and_c_high_implies_both_inputs_high: assert property (
        @(posedge CLK) (Y == 1'b1) && (C == 1'b1) |-> (A == 1'b1) && (B == 1'b1)
    );

    // If Y is HIGH while A is LOW, then C must be LOW.
    check_y_high_and_a_low_implies_c_low: assert property (
        @(posedge CLK) (Y == 1'b1) && (A == 1'b0) |-> (C == 1'b0)
    );

    // If Y is HIGH while B is LOW, then C must be LOW.
    check_y_high_and_b_low_implies_c_low: assert property (
        @(posedge CLK) (Y == 1'b1) && (B == 1'b0) |-> (C == 1'b0)
    );

    // If A, B, and C are stable, Y remains stable.
    check_stable_inputs_keep_y_stable: assert property (
        @(posedge CLK) $stable(A) && $stable(B) && $stable(C) |-> $stable(Y)
    );

    // A falling edge on C forces Y HIGH (due to !C term).
    check_c_fall_forces_y_high: assert property (
        @(posedge CLK) $fell(C) |-> (Y == 1'b1)
    );

    // With C HIGH, a rising A when B is HIGH sets Y HIGH.
    check_c_high_a_rise_with_b1_sets_y: assert property (
        @(posedge CLK) (C == 1'b1) && $rose(A) && (B == 1'b1) |-> (Y == 1'b1)
    );

    // With C HIGH, a rising B when A is HIGH sets Y HIGH.
    check_c_high_b_rise_with_a1_sets_y: assert property (
        @(posedge CLK) (C == 1'b1) && $rose(B) && (A == 1'b1) |-> (Y == 1'b1)
    );

    // With C HIGH, a falling A clears Y LOW.
    check_c_high_a_fall_clears_y: assert property (
        @(posedge CLK) (C == 1'b1) && $fell(A) |-> (Y == 1'b0)
    );

    // With C HIGH, a falling B clears Y LOW.
    check_c_high_b_fall_clears_y: assert property (
        @(posedge CLK) (C == 1'b1) && $fell(B) |-> (Y == 1'b0)
    );
endmodule