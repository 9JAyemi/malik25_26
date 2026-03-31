module calculator_sva (
    input logic clk,
    input logic [3:0] num1,
    input logic [3:0] num2,
    input logic op,
    input logic reset,
    input logic [3:0] result
);

// Reset forces result to zero.
    check_reset_clears_result: assert property (
        @(posedge clk) reset |-> (result == 4'h0)
    );

// In add mode, result equals num1 + num2 (4-bit wrap).
    check_add_mode_result: assert property (
        @(posedge clk) disable iff (reset) (!op) |-> (result == (num1 + num2))
    );

// In subtract mode, result equals num1 - num2 (4-bit wrap).
    check_sub_mode_result: assert property (
        @(posedge clk) disable iff (reset) op |-> (result == (num1 - num2))
    );

// In add mode with equal operands, result is zero.
    check_add_equal_operands_zero: assert property (
        @(posedge clk) disable iff (reset) (!op && (num1 == num2)) |-> (result == 4'h0)
    );

// In subtract mode with equal operands, result is zero.
    check_sub_equal_operands_zero: assert property (
        @(posedge clk) disable iff (reset) (op && (num1 == num2)) |-> (result == 4'h0)
    );

// In add mode, result equals num1 + num2 (4-bit wrap).
    check_add_mode_result: assert property (
        @(posedge clk) disable iff (reset) (!op) |-> (result == (num1 + num2))
    );

// In subtract mode, result equals num1 - num2 (4-bit wrap).
    check_sub_mode_result: assert property (
        @(posedge clk) disable iff (reset) op |-> (result == (num1 - num2))
    );

// In add mode, result equals num1 + num2 (4-bit wrap).
    check_add_mode_result: assert property (
        @(posedge clk) disable iff (reset) (!op) |-> (result == (num1 + num2))
    );

// In subtract mode, result equals num1 - num2 (4-bit wrap).
    check_sub_mode_result: assert property (
        @(posedge clk) disable iff (reset) op |-> (result == (num1 - num2))
    );

endmodule
