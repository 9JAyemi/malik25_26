module MUX2X1 (A, B, S, Y);
input  A ;
input  B ;
input  S ;
output Y ;

   wire  notS;
   assign notS = ~S;

   wire  I0_out, I1_out;
   and   (I0_out, A, notS);
   and   (I1_out, B, S);

   or    (Y, I0_out, I1_out);

endmodule

module MUX4X1 (A, B, C, D, S0, S1, Y);
input  A ;
input  B ;
input  C ;
input  D ;
input  S0 ;
input  S1 ;
output Y ;

   wire  MUX2X1_1_out, MUX2X1_2_out;

   MUX2X1 MUX2X1_1 (A, B, S0, MUX2X1_1_out);
   MUX2X1 MUX2X1_2 (C, D, S0, MUX2X1_2_out);
   MUX2X1 MUX2X1_3 (MUX2X1_1_out, MUX2X1_2_out, S1, Y);

endmodule