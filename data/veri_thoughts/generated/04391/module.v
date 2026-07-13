module mux4to1 (Y, A, B, C, D, S0, S1);
   input A, B, C, D, S0, S1;
   output Y;

   assign Y = (S1 & S0) ? D : (S1 & ~S0) ? C : (~S1 & S0) ? B : A;

endmodule