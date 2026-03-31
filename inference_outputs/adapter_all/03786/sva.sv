module comparator_sva (
    input logic [3:0] A,
    input logic [3:0] B,
    input logic EQ,
    input logic GT
);

    // EQ must reflect whether A and B are equal.
    check_eq_matches_equality: assert property (
        @($global_clock) EQ == (A == B)
    );

    // GT must reflect whether A is greater than B.
    check_gt_matches_greater_than: assert property (
        @($global_clock) GT == (A > B)
    );

    // Equal inputs must drive EQ high and GT low.
    check_equal_inputs_drive_outputs: assert property (
        @($global_clock) (A == B) |-> (EQ && !GT)
    );

    // A greater than B must drive GT high and EQ low.
    check_greater_than_inputs_drive_outputs: assert property (
        @($global_clock) (A > B) |-> (GT && !EQ)
    );

    // A less than B must drive both outputs low.
    check_less_than_inputs_drive_outputs: assert property (
        @($global_clock) (A < B) |-> (!EQ && !GT)
    );

    // EQ and GT cannot be high at the same time.
    check_outputs_not_both_high: assert property (
        @($global_clock) !(EQ && GT)
    );

endmodule