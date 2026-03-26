module mux_2_1 (A, B, S, MO);
   input A, B, S;
   output MO;

   wire not_S;
   assign not_S = ~S;

   assign MO = (not_S & A) | (S & B);
endmodule