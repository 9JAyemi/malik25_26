module comparator_sva (
    input logic [3:0] A,
    input logic [3:0] B,
    input logic greater,
    input logic less
);

    // greater must reflect A > B.
    check_greater_definition: assert property (
        @($global_clock) greater == (A > B)
    );

    // less must reflect A < B.
    check_less_definition: assert property (
        @($global_clock) less == (A < B)
    );

    // greater and less cannot be high together.
    check_compare_outputs_mutex: assert property (
        @($global_clock) !(greater && less)
    );

    // When A equals B, both compare outputs must be low.
    check_equal_inputs_outputs_low: assert property (
        @($global_clock) (A == B) |-> (!greater && !less)
    );

    // When A is greater than B, only greater can be high.
    check_greater_case: assert property (
        @($global_clock) (A > B) |-> (greater && !less)
    );

    // When A is less than B, only less can be high.
    check_less_case: assert property (
        @($global_clock) (A < B) |-> (!greater && less)
    );

endmodule