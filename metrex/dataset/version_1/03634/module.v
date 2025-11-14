module counter (
   // Inputs
   clk,
   // Outputs
   count
   );

   input clk;
   output reg [9:0] count;

   always @ (posedge clk) begin
      if (count == 999) begin
         count <= 0;
      end
      else begin
         count <= count + 1;
      end
   end

endmodule