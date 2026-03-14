module bitwise_op(
  input [7:0] a,
  input [7:0] b,
  input [2:0] op,
  output reg [7:0] out
);

  always @* begin
    case(op)
      3'b000: out = a & b; // bitwise AND
      3'b001: out = a | b; // bitwise OR
      3'b010: out = a ^ b; // bitwise XOR
      3'b011: out = ~a + 1; // 2's complement of a
      3'b100: out = ~b + 1; // 2's complement of b
      3'b101: out = ~(a & b); // bitwise NAND
      3'b110: out = ~(a | b); // bitwise NOR
      3'b111: out = ~(a ^ b); // bitwise XNOR
      default: out = 8'b0;
    endcase
  end

endmodule