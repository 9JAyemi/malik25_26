module comparator_sva (
    input logic [3:0] A,
    input logic [3:0] B,
    input logic greater,
    input logic less
);

    // greater matches the A > B comparison.
    check_greater_definition: assert property (
        @($global_clock) greater == (A > B)
    );

    // less matches the A < B comparison.
    check_less_definition: assert property (
        @($global_clock) less == (A < B)
    );

    // The two outputs are never asserted together.
    check_outputs_mutually_exclusive: assert property (
        @($global_clock) !(greater && less)
    );

    // Equal inputs drive both outputs low.
    check_equal_case_outputs_low: assert property (
        @($global_clock) (A == B) |-> (!greater && !less)
    );

    // Unequal inputs drive exactly one output high.
    check_unequal_case_onehot: assert property (
        @($global_clock) (A != B) |-> (greater ^ less)
    );

endmodule