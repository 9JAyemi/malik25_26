module FADDX2_sva (
    input logic A,
    input logic B,
    input logic CI,
    input logic CO,
    input logic S,
    input logic VDD,
    input logic VSS
);

    // Sum output matches the XOR of the three inputs.
    check_sum_xor: assert property (
        @($global_clock) S == (A ^ B ^ CI)
    );

    // Carry output matches the implemented carry equation.
    check_carry_equation: assert property (
        @($global_clock) CO == ((A & B) | (CI & (A ^ B)))
    );

    // Combined outputs match 2-bit addition of the three 1-bit inputs.
    check_full_adder_vector_sum: assert property (
        @($global_clock) {CO, S} == ({1'b0, A} + {1'b0, B} + {1'b0, CI})
    );

    // When A and B are equal, sum follows CI and carry follows A.
    check_equal_ab_behavior: assert property (
        @($global_clock) (A == B) |-> ((S == CI) && (CO == A))
    );

    // When A and B differ, sum is the inverse of CI and carry follows CI.
    check_unequal_ab_behavior: assert property (
        @($global_clock) (A != B) |-> ((S == ~CI) && (CO == CI))
    );

    // All-zero inputs produce zero sum and zero carry.
    check_all_zero_case: assert property (
        @($global_clock) (~A && ~B && ~CI) |-> (~CO && ~S)
    );

    // All-one inputs produce carry one and sum zero.
    check_all_one_case: assert property (
        @($global_clock) (A && B && CI) |-> (CO && ~S)
    );

    // Any exactly-two-high input combination produces carry one and sum zero.
    check_two_high_case: assert property (
        @($global_clock) ((A && B && ~CI) || (A && ~B && CI) || (~A && B && CI)) |-> (CO && ~S)
    );

endmodule