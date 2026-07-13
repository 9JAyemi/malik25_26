module bitwise_shift(a, y);
  input [31:0] a;
  output [31:0] y;

  assign y = 12345 >> a;

endmodule