module calculator_sva (
    input logic clk,
    input logic [7:0] A,
    input logic [7:0] B,
    input logic [1:0] op,
    input logic [15:0] result
);

// Addition mode returns the 8-bit sum zero-extended to 16 bits.
    check_addition_result: assert property (
        @(posedge clk) (op == 2'b00) |-> (result == {8'h00, A + B})
    );

// Subtraction mode returns the 8-bit difference zero-extended to 16 bits.
    check_subtraction_result: assert property (
        @(posedge clk) (op == 2'b01) |-> (result == {8'h00, A - B})
    );

endmodule
