module max_finder_sva (
    input logic signed [7:0] A,
    input logic signed [7:0] B,
    input logic signed [7:0] C,
    input logic signed [7:0] max_val
);

    // max_val must match the implemented compare tree.
    check_max_expression: assert property (
        @($global_clock)
        max_val == ((A > B) ? ((A > C) ? A : C) : ((B > C) ? B : C))
    );

    // A is chosen only when it is strictly greater than B and C.
    check_a_selected_when_strictly_greatest: assert property (
        @($global_clock)
        ((A > B) && (A > C)) |-> (max_val == A)
    );

    // B is chosen when A does not exceed B and B exceeds C.
    check_b_selected_when_b_branch_wins: assert property (
        @($global_clock)
        ((A <= B) && (B > C)) |-> (max_val == B)
    );

    // C is chosen when it is not smaller than either A or B.
    check_c_selected_when_c_is_not_smaller: assert property (
        @($global_clock)
        ((C >= A) && (C >= B)) |-> (max_val == C)
    );

    // max_val must be at least A.
    check_max_not_less_than_a: assert property (
        @($global_clock)
        max_val >= A
    );

    // max_val must be at least B.
    check_max_not_less_than_b: assert property (
        @($global_clock)
        max_val >= B
    );

    // max_val must be at least C.
    check_max_not_less_than_c: assert property (
        @($global_clock)
        max_val >= C
    );

    // max_val must always match one of the inputs.
    check_max_matches_one_input: assert property (
        @($global_clock)
        (max_val == A) || (max_val == B) || (max_val == C)
    );

    // An A/B tie above C resolves to B.
    check_ab_tie_prefers_b: assert property (
        @($global_clock)
        ((A == B) && (B > C)) |-> (max_val == B)
    );

    // A full tie resolves to C.
    check_all_equal_prefers_c: assert property (
        @($global_clock)
        ((A == B) && (B == C)) |-> (max_val == C)
    );

endmodule