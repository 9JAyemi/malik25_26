
module binary_counter (
   input clk,
   input rst,
   input enable,
   output reg [3:0] count
);

   always @(posedge clk or negedge rst) begin
      if (!rst) begin
         count <= 4'b0;
      end else if (enable) begin
         count <= count + 1;
      end else if (count == 4'b1111) begin
         count <= 4'b0;
      end else begin
         count <= count + 1;
      end
   end

endmodule