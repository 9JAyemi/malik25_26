module comparator_sva (
    input logic       clk,
    input logic [2:0] A,
    input logic [2:0] B,
    input logic       EQ,
    input logic       GT,
    input logic       LT
);

    // Equal inputs must assert only EQ.
    check_equal_case: assert property (
        @(posedge clk) (A == B) |-> (EQ && !GT && !LT)
    );

    // A greater than B must assert only GT.
    check_greater_case: assert property (
        @(posedge clk) (A > B) |-> (!EQ && GT && !LT)
    );

    // A less than B must assert only LT.
    check_less_case: assert property (
        @(posedge clk) (A < B) |-> (!EQ && !GT && LT)
    );

    // EQ can only be high when A equals B.
    check_eq_implies_equal: assert property (
        @(posedge clk) EQ |-> (A == B)
    );

    // GT can only be high when A is greater than B.
    check_gt_implies_greater: assert property (
        @(posedge clk) GT |-> (A > B)
    );

    // LT can only be high when A is less than B.
    check_lt_implies_less: assert property (
        @(posedge clk) LT |-> (A < B)
    );

    // Exactly one comparison result must be asserted.
    check_result_onehot: assert property (
        @(posedge clk) $onehot({EQ, GT, LT})
    );

endmodule