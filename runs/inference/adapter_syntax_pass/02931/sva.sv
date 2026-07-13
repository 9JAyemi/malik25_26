module comparator_sva (
    input logic [3:0] a,
    input logic [3:0] b,
    input logic gt,
    input logic lt,
    input logic eq
);

    // gt must be high exactly when a is greater than b.
    check_gt_definition: assert property (
        @($global_clock) gt == (a > b)
    );

    // lt must be high exactly when a is less than b.
    check_lt_definition: assert property (
        @($global_clock) lt == (a < b)
    );

    // eq must be high exactly when a equals b.
    check_eq_definition: assert property (
        @($global_clock) eq == (a == b)
    );

    // gt and lt cannot be high at the same time.
    check_gt_lt_mutex: assert property (
        @($global_clock) !(gt && lt)
    );

    // eq must be low whenever gt or lt is high.
    check_eq_exclusive_when_gt_or_lt: assert property (
        @($global_clock) !(eq && (gt || lt))
    );

    // When a is greater than b, only gt can be high.
    check_gt_only_when_a_gt_b: assert property (
        @($global_clock) (a > b) |-> (gt && !lt && !eq)
    );

    // When a is less than b, only lt can be high.
    check_lt_only_when_a_lt_b: assert property (
        @($global_clock) (a < b) |-> (!gt && lt && !eq)
    );

    // When a equals b, only eq can be high.
    check_eq_only_when_a_eq_b: assert property (
        @($global_clock) (a == b) |-> (!gt && !lt && eq)
    );

endmodule