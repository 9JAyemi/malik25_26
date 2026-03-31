module comparator_sva (
    input logic [3:0] A,
    input logic [3:0] B,
    input logic [3:0] C,
    input logic [3:0] D,
    input logic       EQ,
    input logic       GT
);

    // EQ must match the three-input equality function.
    check_eq_definition: assert property (
        @($global_clock) EQ == ((A == B) && (B == C) && (C == D))
    );

    // GT must match the RTL OR-of-greater-than function.
    check_gt_definition: assert property (
        @($global_clock) GT == ((A > B) || ((A == B) && (C > D)))
    );

    // If A is greater than B, GT must be high.
    check_gt_when_a_gt_b: assert property (
        @($global_clock) (A > B) |-> GT
    );

    // If A equals B and C is greater than D, GT must be high.
    check_gt_when_a_eq_b_and_c_gt_d: assert property (
        @($global_clock) ((A == B) && (C > D)) |-> GT
    );

    // If A is less than B, GT must be low.
    check_gt_low_when_a_lt_b: assert property (
        @($global_clock) (A < B) |-> !GT
    );

    // If A and B differ and C equals D, GT must be low.
    check_gt_low_when_a_ne_b_and_c_eq_d: assert property (
        @($global_clock) ((A != B) && (C == D)) |-> !GT
    );

    // If all inputs are equal, EQ must be high.
    check_eq_when_all_inputs_equal: assert property (
        @($global_clock) ((A == B) && (B == C) && (C == D)) |-> EQ
    );

    // If any pair of inputs differ, EQ must be low.
    check_eq_low_when_any_pair_differs: assert property (
        @($global_clock) ((A != B) || (B != C) || (C != D)) |-> !EQ
    );

endmodule