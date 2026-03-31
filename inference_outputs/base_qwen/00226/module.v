module desxor1(e, k, b1x, b2x, b3x, b4x, b5x, b6x, b7x, b8x);
  input [47:0] e, k;
  output [5:0] b1x, b2x, b3x, b4x, b5x, b6x, b7x, b8x;
  wire [47:0] XX;
  
  assign XX = k ^ e;
  assign b1x = XX[5:0];
  assign b2x = XX[11:6];
  assign b3x = XX[17:12];
  assign b4x = XX[23:18];
  assign b5x = XX[29:24];
  assign b6x = XX[35:30];
  assign b7x = XX[41:36];
  assign b8x = XX[47:42];
  
endmodule