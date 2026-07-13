
module mux_4_1 (
  input  A, B, C, D,
  input  [1:0] S,
  output Y
);

  wire Y1, Y2;

  assign Y1 = (S == 2'b00) ? A : B;
  assign Y2 = (S == 2'b01) ? C : D;
  assign Y = (S == 2'b10) ? Y1 : Y2;
endmodule