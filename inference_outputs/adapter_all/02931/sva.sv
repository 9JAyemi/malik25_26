module comparator_sva (
    input logic [3:0] a,
    input logic [3:0] b,
    input logic gt,
    input logic lt,
    input logic eq
);

    // No RTL clock or reset; sample this combinational logic on the formal global clock.

    // When a is greater than b, only gt can be asserted.
    check_gt_when_a_gt_b: assert property (
        @($global_clock) (a > b) |-> (gt && !lt && !eq)
    );

    // When a is less than b, only lt can be asserted.
    check_lt_when_a_lt_b: assert property (
        @($global_clock) (a < b) |-> (!gt && lt && !eq)
    );

    // When a equals b, only eq can be asserted.
    check_eq_when_a_eq_b: assert property (
        @($global_clock) (a == b) |-> (!gt && !lt && eq)
    );

    // gt and lt are never asserted together.
    check_gt_lt_mutex: assert property (
        @($global_clock) !(gt && lt)
    );

    // gt and eq are never asserted together.
    check_gt_eq_mutex: assert property (
        @($global_clock) !(gt && eq)
    );

    // lt and eq are never asserted together.
    check_lt_eq_mutex: assert property (
        @($global_clock) !(lt && eq)
    );

    // At least one result output is always asserted.
    check_one_result_asserted: assert property (
        @($global_clock) (gt || lt || eq)
    );

endmodule