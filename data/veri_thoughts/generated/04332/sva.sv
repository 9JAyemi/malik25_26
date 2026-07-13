module half_adder_sva (
    input logic A,
    input logic B,
    input logic S,
    input logic C
);

    // Sum matches the implemented half-adder expression.
    check_sum_function: assert property (
        @($global_clock) S == ((~A & B) | (A & ~B))
    );

    // Carry is high only when both inputs are high.
    check_carry_function: assert property (
        @($global_clock) C == (A & B)
    );

    // Both outputs are low when both inputs are low.
    check_zero_inputs_clear_outputs: assert property (
        @($global_clock) (!A && !B) |-> (!S && !C)
    );

    // Different inputs produce sum without carry.
    check_diff_inputs_sum_only: assert property (
        @($global_clock) (A ^ B) |-> (S && !C)
    );

    // Both high inputs produce carry without sum.
    check_one_one_carry_only: assert property (
        @($global_clock) (A && B) |-> (!S && C)
    );

endmodule