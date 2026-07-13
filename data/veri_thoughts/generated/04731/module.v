module bit_shift (
  input [31:0] in,
  input [4:0] shift,
  input [1:0] op,
  output [31:0] out
);

  reg [31:0] shift_reg;

  always @(*) begin
    case (op)
      2'b00: shift_reg = in << shift;
      2'b01: shift_reg = in >> shift;
      2'b10: shift_reg = $signed(in) >>> shift;
      default: shift_reg = in;
    endcase
  end

  assign out = shift_reg;

endmodule