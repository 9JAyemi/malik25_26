
module AND3 (A, B, C, Z);
input  A ;
input  B ;
input  C ;
output Z ;

   wire  I0_out;
   wire  I1_out;

   and  (I0_out, A, B);
   and  (I1_out, I0_out, C);
   assign Z = I1_out;

endmodule