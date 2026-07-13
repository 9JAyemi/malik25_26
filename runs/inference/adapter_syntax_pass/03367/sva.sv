module calculator_sva (
    input logic [3:0] num1,
    input logic [3:0] num2,
    input logic       op,
    input logic       reset,
    input logic [3:0] result
);

    // Reset forces the result to zero.
    check_reset_clears_result: assert property (
        @($global_clock) reset |-> (result == 4'h0)
    );

    // In add mode, result is the 4-bit sum of num1 and num2.
    check_add_mode_result: assert property (
        @($global_clock) disable iff (reset)
        (!op) |-> (result == ((num1 + num2) & 4'hF))
    );

    // In subtract mode, result is the 4-bit difference of num1 and num2.
    check_subtract_mode_result: assert property (
        @($global_clock) disable iff (reset)
        op |-> (result == ((num1 - num2) & 4'hF))
    );

    // In add mode, adding zero on num2 leaves num1 unchanged.
    check_add_zero_identity: assert property (
        @($global_clock) disable iff (reset)
        (!op && (num2 == 4'h0)) |-> (result == num1)
    );

    // In subtract mode, subtracting zero leaves num1 unchanged.
    check_subtract_zero_identity: assert property (
        @($global_clock) disable iff (reset)
        op && (num2 == 4'h0) |-> (result == num1)
    );

    // In subtract mode, equal operands produce zero.
    check_subtract_equal_operands_zero: assert property (
        @($global_clock) disable iff (reset)
        op && (num1 == num2) |-> (result == 4'h0)
    );

endmodule