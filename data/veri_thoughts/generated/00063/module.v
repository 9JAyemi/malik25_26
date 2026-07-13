module binary_counter(
   input clk,
   input rst,
   input [15:0] max_count,
   output reg [15:0] count,
   output reg done
   );

   always @(posedge clk or posedge rst) begin
      if (rst) begin
         count <= 0;
         done <= 0;
      end
      else begin
         if (count == max_count) begin
            count <= 0;
            done <= 1;
         end
         else begin
            count <= count + 1;
            done <= 0;
         end
      end
   end

endmodule