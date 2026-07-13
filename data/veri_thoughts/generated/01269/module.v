
module comb_circuit (
  input [2:0] A,
  input [2:0] B,
  input [2:0] C,
  output [2:0] Y1,
  output [2:0] Y2,
  output [2:0] Y3
);

  wire [2:0] _Y1;
  wire [2:0] _Y2;
  wire [2:0] _Y3;

  assign _Y1 = A & B;
  assign _Y2 = A | C;
  assign _Y3 = B ^ C;

  assign Y1 = _Y1;
  assign Y2 = _Y2;
  assign Y3 = _Y3;

endmodule
