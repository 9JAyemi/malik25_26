module calculator (
  input [7:0] A,
  input [7:0] B,
  input [1:0] op,
  output reg [7:0] result
);

always @(*) begin
  case(op)
    2'b00: result = A + B;
    2'b01: result = A - B;
    2'b10: result = A * B;
    2'b11: result = A / B;
  endcase
end

endmodule