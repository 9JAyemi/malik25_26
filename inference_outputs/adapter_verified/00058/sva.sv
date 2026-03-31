module calculator_sva (
    input logic clk,
    input logic [7:0] num1,
    input logic [7:0] num2,
    input logic [1:0] op,
    input logic [7:0] result
);

// Addition mode returns the 8-bit sum.
    check_add_result: assert property (
        @(posedge clk) (op == 2'b00) |-> (result == (num1 + num2))
    );

// Subtraction mode returns the 8-bit difference.
    check_sub_result: assert property (
        @(posedge clk) (op == 2'b01) |-> (result == (num1 - num2))
    );

endmodule
