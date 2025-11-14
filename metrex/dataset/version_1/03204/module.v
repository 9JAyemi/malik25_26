module mux4(
   // Outputs
   output reg [DW-1:0] out,
   // Inputs
   input [DW-1:0]  in0,
   input [DW-1:0]  in1,
   input [DW-1:0]  in2,
   input [DW-1:0]  in3,
   input           sel0,
   input           sel1,
   input           sel2,
   input           sel3
   );

   parameter DW=99;
  
   always @(*) begin
      out = ({(DW){sel0}} & in0 |
             {(DW){sel1}} & in1 |
             {(DW){sel2}} & in2 |
             {(DW){sel3}} & in3);
   end

endmodule