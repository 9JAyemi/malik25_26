module top_module_sva (
    input logic [15:0] A,
    input logic [15:0] B,
    input logic [3:0]  shift_amount,
    input logic [15:0] result
);

    // Result must match the implemented comparator-and-shift function.
    check_result_function: assert property (
        @($global_clock)
        result == ((A > B) ? (A << shift_amount) : ((A < B) ? (B >> shift_amount) : A))
    );

    // When A is greater than B, result is A shifted left by shift_amount.
    check_shift_when_a_gt_b: assert property (
        @($global_clock)
        (A > B) |-> (result == (A << shift_amount))
    );

    // When A is less than B, result is B shifted right by shift_amount.
    check_shift_when_a_lt_b: assert property (
        @($global_clock)
        (A < B) |-> (result == (B >> shift_amount))
    );

    // When A equals B, result passes A through.
    check_passthrough_when_equal: assert property (
        @($global_clock)
        (A == B) |-> (result == A)
    );

    // A zero shift amount forces the equal-path passthrough.
    check_zero_shift_passthrough: assert property (
        @($global_clock)
        (A == B) && (shift_amount == 4'd0) |-> (result == A)
    );

    // A zero shift amount forces the greater-than path to pass A through.
    check_zero_shift_a_gt_b_passthrough: assert property (
        @($global_clock)
        (A > B) && (shift_amount == 4'd0) |-> (result == A)
    );

    // A zero shift amount forces the less-than path to pass B through.
    check_zero_shift_a_lt_b_passthrough: assert property (
        @($global_clock)
        (A < B) && (shift_amount == 4'd0) |-> (result == B)
    );

    // A zero shift amount makes the less-than path return zero.
    check_zero_shift_a_lt_b_zero: assert property (
        @($global_clock)
        (A < B) && (shift_amount == 4'd0) |-> (result == 16'h0000)
    );

endmodule