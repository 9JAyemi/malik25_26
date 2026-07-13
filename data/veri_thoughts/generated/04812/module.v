
module counter (
   input clk,
   output reg [3:0] count
);

   reg [3:0] next_count;
   always @ (posedge clk) begin
      count <= next_count;
   end

   always @ (*) begin
      next_count = (count == 4'd15) ? 4'd0 : count + 1;
   end

endmodule