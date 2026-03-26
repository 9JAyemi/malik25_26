module SUB_sva (
    input logic [15:0] a,
    input logic [15:0] b,
    input logic [15:0] sub,
    input logic carry,
    input logic overflow
);

    // sub always reflects the 16-bit result of a - b.
    check_sub_matches_difference: assert property (
        @($global_clock) disable iff (1'b0)
        sub == (a - b)
    );

    // carry is high exactly when a is less than b.
    check_carry_matches_less_than: assert property (
        @($global_clock) disable iff (1'b0)
        carry == (a < b)
    );

    // overflow matches the implemented sign-comparison logic.
    check_overflow_matches_rtl_expression: assert property (
        @($global_clock) disable iff (1'b0)
        overflow == ((sub[15] != a[15]) && (sub[15] != b[15]))
    );

    // A borrow condition drives carry high.
    check_carry_high_on_borrow: assert property (
        @($global_clock) disable iff (1'b0)
        (a < b) |-> carry
    );

    // No borrow condition drives carry low.
    check_carry_low_without_borrow: assert property (
        @($global_clock) disable iff (1'b0)
        (a >= b) |-> !carry
    );

    // Equal operands produce zero and no carry.
    check_equal_inputs_zero_result: assert property (
        @($global_clock) disable iff (1'b0)
        (a == b) |-> (sub == 16'h0000 && !carry)
    );

    // Subtracting zero passes a through with no carry or overflow.
    check_zero_b_passthrough: assert property (
        @($global_clock) disable iff (1'b0)
        (b == 16'h0000) |-> (sub == a && !carry && !overflow)
    );

    // Matching sub and a sign forces overflow low.
    check_overflow_low_when_sub_sign_matches_a: assert property (
        @($global_clock) disable iff (1'b0)
        (sub[15] == a[15]) |-> !overflow
    );

    // Matching sub and b sign forces overflow low.
    check_overflow_low_when_sub_sign_matches_b: assert property (
        @($global_clock) disable iff (1'b0)
        (sub[15] == b[15]) |-> !overflow
    );

endmodule