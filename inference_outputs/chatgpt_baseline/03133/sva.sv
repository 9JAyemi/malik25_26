module min_max_sva #(
    parameter int n = 8
)(
    input logic [n-1:0] in,
    input logic [n-1:0] min,
    input logic [n-1:0] max
);

    // No RTL clock or reset exists; sample combinational invariants on the global formal clock.

    // min equals the minimum bit value present on the input vector.
    check_min_matches_reduction_and: assert property (
        @($global_clock) min == (&in)
    );

    // max equals the maximum bit value present on the input vector.
    check_max_matches_reduction_or: assert property (
        @($global_clock) max == (|in)
    );

    // min never numerically exceeds max.
    check_min_not_greater_than_max: assert property (
        @($global_clock) min <= max
    );

    // An all-zero input drives both outputs to 0.
    check_all_zero_input_outputs_zero: assert property (
        @($global_clock) (~|in) |-> (min == 1'b0 && max == 1'b0)
    );

    // An all-one input drives both outputs to value 1.
    check_all_one_input_outputs_one: assert property (
        @($global_clock) (&in) |-> (min == 1'b1 && max == 1'b1)
    );

    // A mixed input drives min to 0 and max to 1.
    check_mixed_input_outputs_split: assert property (
        @($global_clock) ((|in) && !(&in)) |-> (min == 1'b0 && max == 1'b1)
    );

endmodule