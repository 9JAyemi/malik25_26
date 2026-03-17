module smallest_number_sva (
    input logic [3:0] A,
    input logic [3:0] B,
    input logic [3:0] C,
    input logic [3:0] smallest
);

    // smallest must match the RTL's minimum-selection function.
    check_smallest_function: assert property (
        @($global_clock)
        smallest == ((A <= B && A <= C) ? A :
                     ((B <= A && B <= C) ? B : C))
    );

    // smallest must not be greater than A.
    check_smallest_le_a: assert property (
        @($global_clock)
        smallest <= A
    );

    // smallest must not be greater than B.
    check_smallest_le_b: assert property (
        @($global_clock)
        smallest <= B
    );

    // smallest must not be greater than C.
    check_smallest_le_c: assert property (
        @($global_clock)
        smallest <= C
    );

    // smallest must equal one of the three inputs.
    check_smallest_matches_input: assert property (
        @($global_clock)
        (smallest == A) || (smallest == B) || (smallest == C)
    );

    // If A is no larger than both others, smallest must equal A.
    check_select_a_when_a_is_min: assert property (
        @($global_clock)
        (A <= B && A <= C) |-> (smallest == A)
    );

    // If B is no larger than both others, smallest must equal B.
    check_select_b_when_b_is_min: assert property (
        @($global_clock)
        (B <= A && B <= C) |-> (smallest == B)
    );

    // If C is no larger than both others, smallest must equal C.
    check_select_c_when_c_is_min: assert property (
        @($global_clock)
        (C <= A && C <= B) |-> (smallest == C)
    );

endmodule