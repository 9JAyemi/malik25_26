module comparator_sva (
    input logic [3:0] A,
    input logic [3:0] B,
    input logic greater,
    input logic less
);

    // greater must match the RTL comparison.
    check_greater_definition: assert property (
        @($global_clock) greater == (A > B)
    );

    // less must match the RTL comparison.
    check_less_definition: assert property (
        @($global_clock) less == (A < B)
    );

    // greater and less cannot be high together.
    check_outputs_mutually_exclusive: assert property (
        @($global_clock) !(greater && less)
    );

    // When A is greater than B, greater must be high.
    check_greater_high_when_a_gt_b: assert property (
        @($global_clock) (A > B) |-> greater
    );

    // When A is less than B, less must be high.
    check_less_high_when_a_lt_b: assert property (
        @($global_clock) (A < B) |-> less
    );

    // When A equals B, both outputs must be low.
    check_equal_inputs_drive_outputs_low: assert property (
        @($global_clock) (A == B) |-> (!greater && !less)
    );

endmodule