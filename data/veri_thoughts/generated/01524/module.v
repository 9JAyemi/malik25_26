module accumulator
  #(parameter IWIDTH=16, OWIDTH=30)
    (input clk,
     input clear,
     input acc,
     input signed [IWIDTH-1:0] in,
     output reg signed [OWIDTH-1:0] out);

   wire signed [OWIDTH-1:0] in_signext;
   wire signed [OWIDTH-1:0] in_signext_extended;

   assign in_signext_extended = {{OWIDTH-IWIDTH{in[IWIDTH-1]}}, in};

   // CLEAR & ~ACC --> clears the accumulator
   // CLEAR & ACC --> loads the accumulator
   // ~CLEAR & ACC --> accumulates
   // ~CLEAR & ~ACC --> hold

   wire signed [OWIDTH-1:0] addend1 = clear ? 0 : out;
   wire signed [OWIDTH-1:0] addend2 = ~acc ? 0 : in_signext_extended;
   wire signed [OWIDTH-1:0] sum_int = addend1 + addend2;

   always @(posedge clk)
     out <= sum_int;

endmodule