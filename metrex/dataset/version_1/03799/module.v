
module Floating_Point_Arithmetic (
  input [31:0] operand1,
  input [31:0] operand2,
  input [1:0] operation,
  output reg [31:0] result
);

parameter mantissa_width = 23; // width of the mantissa in bits
parameter exponent_width = 8; // width of the exponent in bits
parameter bias = 127; // bias of the exponent field

reg [31:0] add_result, sub_result, mul_result, div_result;
reg [31:0] operand2_neg;

// Negate operand2 for subtraction
always @(*) begin
  operand2_neg = {operand2[31], ~operand2[30:0] + 1'b1};
end

// Floating-point addition
always @(*) begin
  add_result = operand1 + operand2;
end

// Floating-point subtraction
always @(*) begin
  sub_result = operand1 - operand2_neg;
end

// Floating-point multiplication
always @(*) begin
  mul_result = operand1 * operand2;
end

// Floating-point division
always @(*) begin
  div_result = operand1 / operand2;
end

// Select the result based on the operation
always @(*) begin
  case (operation)
    2'b00: result = add_result;
    2'b01: result = sub_result;
    2'b10: result = mul_result;
    2'b11: result = div_result;
    default: result = 32'b0;
  endcase
end

endmodule