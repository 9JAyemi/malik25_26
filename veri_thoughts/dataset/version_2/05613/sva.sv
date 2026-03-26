module max3_sva (
    input logic [31:0] A,
    input logic [31:0] B,
    input logic [31:0] C,
    input logic [31:0] X
);

    // If A is strictly greater than both B and C, X must select A.
    check_select_a_when_a_is_strict_max: assert property (
        @($global_clock) ((A > B) && (A > C)) |-> (X == A)
    );

    // If B is at least A and strictly greater than C, X must select B.
    check_select_b_when_b_is_max: assert property (
        @($global_clock) ((B >= A) && (B > C)) |-> (X == B)
    );

    // If C is at least as large as both A and B, X must select C.
    check_select_c_when_c_is_max_or_tied: assert property (
        @($global_clock) ((C >= A) && (C >= B)) |-> (X == C)
    );

    // X must never be less than A.
    check_x_not_less_than_a: assert property (
        @($global_clock) (X >= A)
    );

    // X must never be less than B.
    check_x_not_less_than_b: assert property (
        @($global_clock) (X >= B)
    );

    // X must never be less than C.
    check_x_not_less_than_c: assert property (
        @($global_clock) (X >= C)
    );

    // X must always equal one of the three inputs.
    check_x_matches_one_input: assert property (
        @($global_clock) ((X == A) || (X == B) || (X == C))
    );

endmodule