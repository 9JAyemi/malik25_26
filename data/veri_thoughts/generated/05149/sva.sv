module comparator_sva (
    input logic       clk,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic [3:0] C,
    input logic [3:0] D,
    input logic       EQ,
    input logic       GT
);

    // EQ matches the all-inputs-equal comparison.
    check_eq_definition: assert property (
        @(posedge clk) EQ == ((A == B) && (B == C) && (C == D))
    );

    // GT matches the comparator decision logic.
    check_gt_definition: assert property (
        @(posedge clk) GT == ((A > B) || ((A == B) && (C > D)))
    );

    // Equal inputs force GT low.
    check_eq_implies_not_gt: assert property (
        @(posedge clk) EQ |-> !GT
    );

    // A greater than B forces GT high.
    check_a_greater_b_sets_gt: assert property (
        @(posedge clk) (A > B) |-> GT
    );

    // A less than B forces GT low.
    check_a_less_b_clears_gt: assert property (
        @(posedge clk) (A < B) |-> !GT
    );

    // With A tied to B, C greater than D forces GT high.
    check_tie_breaker_sets_gt: assert property (
        @(posedge clk) ((A == B) && (C > D)) |-> GT
    );

    // With A tied to B, C not greater than D forces GT low.
    check_tie_breaker_clears_gt: assert property (
        @(posedge clk) ((A == B) && (C <= D)) |-> !GT
    );

    // When A equals B, GT can only come from C greater than D.
    check_gt_with_equal_ab_requires_c_greater_d: assert property (
        @(posedge clk) (GT && (A == B)) |-> (C > D)
    );

    // When A differs from B, GT can only come from A greater than B.
    check_gt_with_unequal_ab_requires_a_greater_b: assert property (
        @(posedge clk) (GT && (A != B)) |-> (A > B)
    );

endmodule