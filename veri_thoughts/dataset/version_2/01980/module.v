
module MUX2x1_8_1_0
   (A,
    B,
    SEL,
    X);
  input [7:0]A;
  input [7:0]B;
  input SEL;
  output [7:0]X;

  assign X = SEL ? B : A;
endmodule
module MUX4x1_8_2_0
   (A,
    B,
    C,
    D,
    SEL,
    X);
  input [7:0]A;
  input [7:0]B;
  input [7:0]C;
  input [7:0]D;
  input [1:0]SEL;
  output [7:0]X;

  wire [7:0]AB;
  wire [7:0]CD;

  assign AB = SEL[1] ? B : A;
  assign CD = SEL[1] ? D : C;
  assign X = SEL[0] ? CD : AB;
endmodule