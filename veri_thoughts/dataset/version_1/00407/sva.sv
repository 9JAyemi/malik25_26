module math_operation_sva (
    input logic [3:0] a,
    input logic [3:0] b,
    input logic [3:0] result
);

    // Result implements a + (2*b) with 4-bit truncation.
    check_result_definition: assert property (
        @($global_clock) result === ((a + (2 * b)) & 4'hF)
    );

    // When b is zero, result must equal a.
    check_zero_b_passthrough: assert property (
        @($global_clock) (b == 4'h0) |-> (result === a)
    );

    // When a is zero, result must equal the 4-bit value of 2*b.
    check_zero_a_double_b: assert property (
        @($global_clock) (a == 4'h0) |-> (result === ((2 * b) & 4'hF))
    );

    // The least-significant bit of result always matches the least-significant bit of a.
    check_lsb_matches_a: assert property (
        @($global_clock) result[0] === a[0]
    );

endmodule