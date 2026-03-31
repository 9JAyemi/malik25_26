module mag_comparator_sva (
    input logic [1:0] A,
    input logic [1:0] B,
    input logic EQ,
    input logic GT,
    input logic LT
);

    // EQ must reflect A == B.
    check_eq_definition: assert property (
        @($global_clock) (EQ == (A == B))
    );

    // GT must reflect A > B.
    check_gt_definition: assert property (
        @($global_clock) (GT == (A > B))
    );

    // LT must reflect A < B.
    check_lt_definition: assert property (
        @($global_clock) (LT == (A < B))
    );

    // EQ and GT cannot be high together.
    check_eq_gt_mutex: assert property (
        @($global_clock) !(EQ && GT)
    );

    // EQ and LT cannot be high together.
    check_eq_lt_mutex: assert property (
        @($global_clock) !(EQ && LT)
    );

    // GT and LT cannot be high together.
    check_gt_lt_mutex: assert property (
        @($global_clock) !(GT && LT)
    );

    // Exactly one of EQ, GT, or LT must be high.
    check_one_relation_high: assert property (
        @($global_clock) (EQ || GT || LT)
    );

    // Equal inputs must drive only EQ high.
    check_equal_case: assert property (
        @($global_clock) (A == B) |-> (EQ && !GT && !LT)
    );

    // Greater-than inputs must drive only GT high.
    check_greater_case: assert property (
        @($global_clock) (A > B) |-> (GT && !EQ && !LT)
    );

    // Less-than inputs must drive only LT high.
    check_less_case: assert property (
        @($global_clock) (A < B) |-> (LT && !EQ && !GT)
    );

endmodule