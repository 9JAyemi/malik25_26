module top_module_sva (
    input logic [3:0] A,
    input logic [3:0] B,
    input logic       carry_in,
    input logic [3:0] sum,
    input logic       carry_out,
    input logic       EQ,
    input logic       GT,
    input logic       LT
);

    // Sum and carry_out match the 5-bit addition of A, B, and carry_in.
    check_adder_result: assert property (
        @($global_clock) {carry_out, sum} == ({1'b0, A} + {1'b0, B} + carry_in)
    );

    // The LSB sum matches the full-adder equation.
    check_sum_bit0: assert property (
        @($global_clock) sum[0] == (A[0] ^ B[0] ^ carry_in)
    );

    // EQ reflects whether A and B are equal.
    check_eq_definition: assert property (
        @($global_clock) EQ == (A == B)
    );

    // GT reflects whether A is greater than B.
    check_gt_definition: assert property (
        @($global_clock) GT == (A > B)
    );

    // LT reflects whether A is less than B.
    check_lt_definition: assert property (
        @($global_clock) LT == (A < B)
    );

    // Comparison outputs are never asserted together.
    check_compare_mutex: assert property (
        @($global_clock) !((EQ && GT) || (EQ && LT) || (GT && LT))
    );

    // One comparison output is always asserted.
    check_compare_complete: assert property (
        @($global_clock) EQ || GT || LT
    );

    // Equal inputs drive only EQ high.
    check_equal_case: assert property (
        @($global_clock) (A == B) |-> (EQ && !GT && !LT)
    );

    // Greater-than inputs drive only GT high.
    check_greater_case: assert property (
        @($global_clock) (A > B) |-> (!EQ && GT && !LT)
    );

    // Less-than inputs drive only LT high.
    check_less_case: assert property (
        @($global_clock) (A < B) |-> (!EQ && !GT && LT)
    );

endmodule