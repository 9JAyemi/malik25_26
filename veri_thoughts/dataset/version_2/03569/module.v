module calculator(input [3:0] a, input [3:0] b, input [1:0] op, output [3:0] add_out, output [3:0] sub_out, output [3:0] mul_out, output [3:0] div_out);

  wire [7:0] prod;

  assign add_out = a + b;
  assign sub_out = a - b;
  assign prod = a * b;
  assign mul_out = prod[7:4];
  assign div_out = (b == 4'h0) ? 4'h0 : a / b;

endmodule