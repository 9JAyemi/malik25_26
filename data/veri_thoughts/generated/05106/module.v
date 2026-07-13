
module BinaryMultiplier (A, B, Z);
input  A ;
input  B ;
output Z ;

   wire A_not, B_not, AB;

   not (A_not, A);
   not (B_not, B);
   and (AB, A_not, B_not);
   not (Z, AB);

endmodule