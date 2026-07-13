module xor3_assertions (
    input logic A,
    input logic B,
    input logic C,
    input logic X
);

    // X must always equal the three-input XOR.
    check_x_matches_three_input_xor: assert property (
        @($global_clock) X == (A ^ B ^ C)
    );

    // If A and B are equal, X must equal C.
    check_x_equals_c_when_a_equals_b: assert property (
        @($global_clock) (A == B) |-> (X == C)
    );

    // If A and C are equal, X must equal B.
    check_x_equals_b_when_a_equals_c: assert property (
        @($global_clock) (A == C) |-> (X == B)
    );

    // If B and C are equal, X must equal A.
    check_x_equals_a_when_b_equals_c: assert property (
        @($global_clock) (B == C) |-> (X == A)
    );

    // If A and B differ, X must be the inverse of C.
    check_x_inverts_c_when_a_differs_b: assert property (
        @($global_clock) (A != B) |-> (X == ~C)
    );

    // If A and C differ, X must be the inverse of B.
    check_x_inverts_b_when_a_differs_c: assert property (
        @($global_clock) (A != C) |-> (X == ~B)
    );

    // If B and C differ, X must be the inverse of A.
    check_x_inverts_a_when_b_differs_c: assert property (
        @($global_clock) (B != C) |-> (X == ~A)
    );

endmodule