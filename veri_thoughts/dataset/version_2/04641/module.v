module Mux4x1_8
  (A,
   B,
   C,
   D,
   SEL,
   X);
  input [7:0] A;
  input [7:0] B;
  input [7:0] C;
  input [7:0] D;
  input [1:0] SEL;
  output [7:0] X;

  reg [7:0] mux_out;

  always @*
  begin
    case (SEL)
      2'b00: mux_out = A;
      2'b01: mux_out = B;
      2'b10: mux_out = C;
      2'b11: mux_out = D;
    endcase
  end

  assign X = mux_out;
endmodule


module RAT_Mux4x1_8_0_1
  (A,
   B,
   C,
   D,
   SEL,
   X);
  input [7:0] A;
  input [7:0] B;
  input [7:0] C;
  input [7:0] D;
  input [1:0] SEL;
  output [7:0] X;

  wire [7:0] mux_out;

  Mux4x1_8 U0
    (.A(A),
     .B(B),
     .C(C),
     .D(D),
     .SEL(SEL),
     .X(mux_out));

  assign X = mux_out;
endmodule