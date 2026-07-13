module max_value_sva (
    input logic [7:0] A,
    input logic [7:0] B,
    input logic [7:0] MAX
);
    // MAX implements the ternary compare result exactly.
    check_function_equivalence: assert property (
        @($global_clock) (MAX == ((A >= B) ? A : B))
    );

    // When A >= B, MAX equals A.
    check_choose_A_when_A_ge_B: assert property (
        @($global_clock) (A >= B) |-> (MAX == A)
    );

    // When A < B, MAX equals B.
    check_choose_B_when_A_lt_B: assert property (
        @($global_clock) (A < B) |-> (MAX == B)
    );

    // If MAX equals A, then A >= B.
    check_if_max_is_A_then_A_ge_B: assert property (
        @($global_clock) (MAX == A) |-> (A >= B)
    );

    // If MAX equals B, then A < B.
    check_if_max_is_B_then_A_lt_B: assert property (
        @($global_clock) (MAX == B) |-> (A < B)
    );

    // MAX is always either A or B.
    check_max_is_either_input: assert property (
        @($global_clock) (MAX == A) || (MAX == B)
    );

    // MAX is greater than or equal to both inputs (unsigned).
    check_max_ge_inputs: assert property (
        @($global_clock) (MAX >= A) && (MAX >= B)
    );

    // Equal inputs drive MAX to that value; tie breaks to A.
    check_tie_breaks_to_A: assert property (
        @($global_clock) (A == B) |-> (MAX == A)
    );

    // If A and B are stable, MAX remains stable.
    check_stable_when_inputs_stable: assert property (
        @($global_clock) ($stable(A) && $stable(B)) |-> $stable(MAX)
    );
endmodule