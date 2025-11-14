
module bmod
  (input  clk,
   input [31:0] n,
   output [31:0] result);

   cmod csub (.clk(clk), .n(n), .result(result));

endmodule

module cmod
  (input  clk,
   input [31:0] n,
   output [31:0] result);

  // Perform some operation on n to get result
  assign result = n + 1;

endmodule
