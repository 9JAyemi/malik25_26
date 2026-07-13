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

    // In add mode, result is the 4-bit sum of num1 and num2.
    check_add_mode_result: assert property (
        @($global_clock) disable iff (reset)
        (!op) |-> (result == (num1 + num2))
    );

    // In subtract mode, result is the 4-bit difference of num1 and num2.
    check_subtract_mode_result: assert property (
        @($global_clock) disable iff (reset)
        op |-> (result == (num1 - num2))
    );

    // With stable inputs, the combinational result remains stable.
    check_stable_inputs_keep_result_stable: assert property (
        @($global_clock) disable iff (reset)
        $stable({num1, num2, op}) |-> $stable(result)
    );

endmodule