module calculator(
  input [2:0] opcode,
  input [7:0] A,
  input [7:0] B,
  output reg [7:0] result
);

  always @(*) begin
    case(opcode)
      3'b000: result = A + B; // addition
      3'b001: result = A - B; // subtraction
      3'b010: result = A * B; // multiplication
      3'b011: result = A / B; // division
      default: result = 0;    // invalid opcode
    endcase
  end

endmodule