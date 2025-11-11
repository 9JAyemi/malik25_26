module addition_module
  (
   input   [1:0] i,
   input   [1:0] a,
   output  [1:0] o
   );
   assign o = i + a;
endmodule