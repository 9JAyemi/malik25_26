module nand3 (
   // Outputs
   zn,
   // Inputs
   a, b, c
   );

   parameter DELAY = 2;
   input a,b,c;
   output zn;

   assign #DELAY zn= !(a & b & c);

endmodule