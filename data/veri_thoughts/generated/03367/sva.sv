module calculator_sva (
    input logic [3:0] num1,
    input logic [3:0] num2,
    input logic       op,
    input logic       reset,
    input logic [3:0] result
);

    // Reset forces the result to zero.
    check_reset_clears_result: assert property (
        @($global_clock) reset |-> (result == 4'b0000)
    );

    // When not in reset and op is low, result is the sum of the inputs.
    check_add_when_op_low: assert property (
        @($global_clock) disable iff (reset) (!op) |-> (result == (num1 + num2))
    );

    // When not in reset and op is high, result is the difference of the inputs.
    check_subtract_when_op_high: assert property (
        @($global_clock) disable iff (reset) op |-> (result == (num1 - num2))
    );

endmodule