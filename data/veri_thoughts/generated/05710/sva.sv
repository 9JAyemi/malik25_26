module comparator_sva (
    input logic [3:0] a,
    input logic [3:0] b,
    input logic eq,
    input logic gt_a,
    input logic gt_b
);

    // eq reflects whether a and b are equal.
    check_eq_matches_equality: assert property (
        @($global_clock) eq == (a == b)
    );

    // gt_a reflects whether a is greater than b.
    check_gt_a_matches_a_greater: assert property (
        @($global_clock) gt_a == (a > b)
    );

    // gt_b reflects whether b is greater than a.
    check_gt_b_matches_b_greater: assert property (
        @($global_clock) gt_b == (b > a)
    );

    // Equal inputs drive only eq high.
    check_equal_inputs_drive_eq_only: assert property (
        @($global_clock) (a == b) |-> (eq && !gt_a && !gt_b)
    );

    // a greater than b drives only gt_a high.
    check_a_greater_drives_gt_a_only: assert property (
        @($global_clock) (a > b) |-> (!eq && gt_a && !gt_b)
    );

    // b greater than a drives only gt_b high.
    check_b_greater_drives_gt_b_only: assert property (
        @($global_clock) (b > a) |-> (!eq && !gt_a && gt_b)
    );

    // No two outputs are high at the same time.
    check_outputs_are_mutually_exclusive: assert property (
        @($global_clock) (!(eq && gt_a) && !(eq && gt_b) && !(gt_a && gt_b))
    );

    // One comparison result is always indicated.
    check_one_output_is_always_high: assert property (
        @($global_clock) (eq || gt_a || gt_b)
    );

endmodule