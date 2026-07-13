module XNOR3HD2X_sva (
    input logic A,
    input logic B,
    input logic C,
    input logic Z
);

    // Z must always implement the 3-input XNOR function.
    check_function_exact: assert property (
        @($global_clock) Z == ~(A ^ B ^ C)
    );

    // If A and B match, Z must be the inverse of C.
    check_equal_ab: assert property (
        @($global_clock) (A == B) |-> (Z == ~C)
    );

    // If B and C match, Z must be the inverse of A.
    check_equal_bc: assert property (
        @($global_clock) (B == C) |-> (Z == ~A)
    );

    // If A and C match, Z must be the inverse of B.
    check_equal_ac: assert property (
        @($global_clock) (A == C) |-> (Z == ~B)
    );

    // If A and B differ, Z must match C.
    check_diff_ab: assert property (
        @($global_clock) (A != B) |-> (Z == C)
    );

    // If B and C differ, Z must match A.
    check_diff_bc: assert property (
        @($global_clock) (B != C) |-> (Z == A)
    );

    // If A and C differ, Z must match B.
    check_diff_ac: assert property (
        @($global_clock) (A != C) |-> (Z == B)
    );

    // When all inputs are low, Z must be high.
    check_all_zero: assert property (
        @($global_clock) (!A && !B && !C) |-> Z
    );

    // When exactly one input is high, Z must be low.
    check_one_hot: assert property (
        @($global_clock) ((A && !B && !C) || (!A && B && !C) || (!A && !B && C)) |-> !Z
    );

    // When exactly two inputs are high, Z must be high.
    check_two_hot: assert property (
        @($global_clock) ((A && B && !C) || (A && !B && C) || (!A && B && C)) |-> Z
    );

    // When all inputs are high, Z must be low.
    check_all_one: assert property (
        @($global_clock) (A && B && C) |-> !Z
    );

endmodule