module mux4to1 (A, B, C, D, S0, S1, Y);
   input [3:0] A, B, C, D;
   input S0, S1;
   output Y;
   
   assign Y = (S1 & S0 & D) | (S1 & ~S0 & C) | (~S1 & S0 & B) | (~S1 & ~S0 & A);
endmodule