
module four_bit_adder (
  input [3:0] A,
  input [3:0] B,
  input Cin,
  output [3:0] Sum,
  output Cout
);

  wire [3:0] sum_wire;
  wire carry_wire;

  assign {carry_wire, sum_wire} = A + B + Cin;
  assign Cout = carry_wire;
  assign Sum = sum_wire;

endmodule