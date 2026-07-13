module mux4to1(A, B, S0, S1, Y);
  input A, B, S0, S1;
  output Y;
  
  wire notS0, notS1;
  
  assign notS0 = ~S0;
  assign notS1 = ~S1;
  
  assign Y = (A & notS0 & notS1) | (B & notS0 & S1) | (A & S0 & notS1) | (B & S0 & S1);
  
endmodule