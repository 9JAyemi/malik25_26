
module adder_subtractor (
  input [3:0] A,
  input [3:0] B,
  input Cin,
  input Mode,
  output [3:0] Sum,
  output Cout
);

  wire [3:0] Adder_out;
  wire [3:0] Sub_out;
  wire [3:0] Twos_comp;
  wire Mode_inv;

  assign Mode_inv = ~Mode;

  // Adder
  assign Adder_out = A + B + Cin;

  // Subtractor
  assign Twos_comp = ~B + 1;
  assign Sub_out = A - Twos_comp + Mode;

  // Multiplexer
  assign Sum = Mode_inv ? Adder_out : Sub_out;

  // Carry out
  assign Cout = Mode_inv ? Adder_out[3] : Sub_out[3];

endmodule