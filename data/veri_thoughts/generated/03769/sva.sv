module ArithmeticOp_sva(
    input logic [7:0]  a,
    input logic [7:0]  b,
    input logic [15:0] result
);

    // Result must match the implemented arithmetic expression.
    check_result_matches_implemented_expression: assert property (
        @($global_clock) result == ((a * b) + (a + b))
    );

    // When a is zero, the result must reduce to b.
    check_zero_a_reduces_to_b: assert property (
        @($global_clock) (a == 8'h00) |-> (result == {8'h00, b})
    );

    // When b is zero, the result must reduce to a.
    check_zero_b_reduces_to_a: assert property (
        @($global_clock) (b == 8'h00) |-> (result == {8'h00, a})
    );

    // 0xFF plus 0x01 must show 8-bit sum wrap behavior.
    check_ff_and_01_sum_wrap_behavior: assert property (
        @($global_clock) ((a == 8'hff) && (b == 8'h01)) |-> (result == 16'h00ff)
    );

    // Maximum operands must produce the expected 16-bit result.
    check_ff_and_ff_maximum_result: assert property (
        @($global_clock) ((a == 8'hff) && (b == 8'hff)) |-> (result == 16'hfeff)
    );

endmodule