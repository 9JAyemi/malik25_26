module calculator (
  input [7:0] a,
  input [7:0] b,
  input [1:0] op,
  output [7:0] result
);

  reg [7:0] result_reg;

  always @(*) begin
    case (op)
      2'b00: result_reg = a + b;
      2'b01: result_reg = a - b;
      2'b10: result_reg = a * b;
      2'b11: result_reg = a / b;
    endcase
  end

  assign result = result_reg;

endmodule