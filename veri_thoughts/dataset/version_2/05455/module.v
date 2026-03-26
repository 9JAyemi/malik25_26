module adder (
   // Inputs
   clk,
   in0,
   in1,
   // Outputs
   out
   );
   input clk;
   input [7:0] in0;
   input [7:0] in1;
   output reg [15:0] out;

   always @ (posedge clk) begin
      out <= in0 + in1;
      if (out === 16'hfffe) begin
         out <= 0;
      end
   end

endmodule