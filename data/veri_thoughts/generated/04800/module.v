
module output_generator(
  input [3:0] num1,
  input [3:0] num2,
  input [1:0] operation,
  output [3:0] result
);

  reg [3:0] result_reg; // declare result as a register

  always @(*) begin
    case(operation)
      2'b00: result_reg = num1 + num2; // addition
      2'b01: result_reg = num1 - num2; // subtraction
      2'b10: result_reg = num1 * num2; // multiplication
      2'b11: result_reg = num1 / num2; // division
      default: result_reg = 4'b0000; // default case
    endcase
  end

  assign result = result_reg; // assign result to the output port

endmodule
