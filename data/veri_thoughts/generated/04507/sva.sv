module max_value_sva (
    input logic [3:0] A,
    input logic [3:0] B,
    input logic [3:0] max
);

    // max must implement the RTL comparison result.
    check_max_function: assert property (
        @($global_clock) disable iff (1'b0) max == ((A > B) ? A : B)
    );

    // When A is greater than B, max must equal A.
    check_select_a_when_a_gt_b: assert property (
        @($global_clock) disable iff (1'b0) (A > B) |-> (max == A)
    );

    // When A is less than or equal to B, max must equal B.
    check_select_b_when_a_le_b: assert property (
        @($global_clock) disable iff (1'b0) (A <= B) |-> (max == B)
    );

    // The output must always be at least A.
    check_max_ge_a: assert property (
        @($global_clock) disable iff (1'b0) (max >= A)
    );

    // The output must always be at least B.
    check_max_ge_b: assert property (
        @($global_clock) disable iff (1'b0) (max >= B)
    );

    // Equal inputs must produce that shared value.
    check_equal_inputs: assert property (
        @($global_clock) disable iff (1'b0) (A == B) |-> ((max == A) && (max == B))
    );

endmodule