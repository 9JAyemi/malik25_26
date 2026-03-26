module comparator_sva (
    input logic        clk,
    input logic [3:0]  A,
    input logic [3:0]  B,
    input logic        EQ,
    input logic        GT,
    input logic        LT
);

    // EQ must be the only asserted output when A equals B.
    check_eq_when_equal: assert property (
        @(posedge clk) (A == B) |-> (EQ && !GT && !LT)
    );

    // GT must be the only asserted output when A is greater than B.
    check_gt_when_greater: assert property (
        @(posedge clk) (A > B) |-> (GT && !EQ && !LT)
    );

    // LT must be the only asserted output when A is less than B.
    check_lt_when_less: assert property (
        @(posedge clk) (A < B) |-> (LT && !EQ && !GT)
    );

    // EQ can only assert for equal inputs.
    check_eq_only_when_equal: assert property (
        @(posedge clk) EQ |-> (A == B)
    );

    // GT can only assert when A is greater than B.
    check_gt_only_when_greater: assert property (
        @(posedge clk) GT |-> (A > B)
    );

    // LT can only assert when A is less than B.
    check_lt_only_when_less: assert property (
        @(posedge clk) LT |-> (A < B)
    );

    // Exactly one comparison result must be asserted each cycle.
    check_outputs_onehot: assert property (
        @(posedge clk) $onehot({EQ, GT, LT})
    );

endmodule