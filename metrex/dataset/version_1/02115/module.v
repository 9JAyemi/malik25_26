
module NOR4X0 (IN1, IN2, IN3, IN4, QN);

   input IN1;
   input IN2, IN3, IN4;
   output QN;

   wire n1, n2, n3, n4;

   nand (n1, IN1, IN2);
   nand (n2, IN3, IN4);
   nand (n3, n1, n2);
   nand (n4, n3, n3);

   nand (QN, n4, n4);

endmodule
