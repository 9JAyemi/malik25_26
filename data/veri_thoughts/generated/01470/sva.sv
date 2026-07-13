module sky130_fd_sc_hdll__nand3_XOR_sva (
    input logic Y,
    input logic A,
    input logic B,
    input logic C
);
    // Functional equivalence sampled on A rising edge.
    check_func_eq_on_A: assert property (
        @(posedge A) Y == ((~C) | (A & B))
    );

    // Functional equivalence sampled on B rising edge.
    check_func_eq_on_B: assert property (
        @(posedge B) Y == ((~C) | (A & B))
    );

    // Functional equivalence sampled on C rising edge.
    check_func_eq_on_C: assert property (
        @(posedge C) Y == ((~C) | (A & B))
    );

    // When C is LOW, Y must be HIGH (sampled on A).
    check_c_low_y_high_on_A: assert property (
        @(posedge A) (C == 1'b0) |-> (Y == 1'b1)
    );

    // When C is LOW, Y must be HIGH (sampled on B).
    check_c_low_y_high_on_B: assert property (
        @(posedge B) (C == 1'b0) |-> (Y == 1'b1)
    );

    // When C is HIGH, Y equals A&B (sampled on A).
    check_c_high_y_eq_ab_on_A: assert property (
        @(posedge A) (C == 1'b1) |-> (Y == (A & B))
    );

    // When C is HIGH, Y equals A&B (sampled on B).
    check_c_high_y_eq_ab_on_B: assert property (
        @(posedge B) (C == 1'b1) |-> (Y == (A & B))
    );

    // If both A and B are HIGH, Y must be HIGH (any C) sampled on A.
    check_ab_both_high_y_high_on_A: assert property (
        @(posedge A) (A == 1'b1 && B == 1'b1) |-> (Y == 1'b1)
    );

    // If both A and B are HIGH, Y must be HIGH (any C) sampled on B.
    check_ab_both_high_y_high_on_B: assert property (
        @(posedge B) (A == 1'b1 && B == 1'b1) |-> (Y == 1'b1)
    );

    // If Y is LOW then C must be HIGH and at least one of A or B is LOW (sampled on A).
    check_y_low_implies_c_high_and_not_ab_on_A: assert property (
        @(posedge A) (Y == 1'b0) |-> ((C == 1'b1) && ((A == 1'b0) || (B == 1'b0)))
    );

    // If Y is HIGH then either C is LOW or both A and B are HIGH (sampled on B).
    check_y_high_implies_c_low_or_ab_on_B: assert property (
        @(posedge B) (Y == 1'b1) |-> ((C == 1'b0) || (A & B))
    );
endmodule