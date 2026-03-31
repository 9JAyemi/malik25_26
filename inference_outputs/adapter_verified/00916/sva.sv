module calculator_sva (
    input logic clk,
    input logic [7:0] a,
    input logic [7:0] b,
    input logic [1:0] op,
    input logic [7:0] result
);

// Addition mode returns the 8-bit sum.
    check_addition_result: assert property (
        @(posedge clk) (op == 2'b00) |-> (result == (a + b))
    );

// Subtraction mode returns the 8-bit difference.
    check_subtraction_result: assert property (
        @(posedge clk) (op == 2'b01) |-> (result == (a - b))
    );

endmodule
