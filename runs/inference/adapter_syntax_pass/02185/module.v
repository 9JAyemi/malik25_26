module counter
   (
    input CLK,
    input reset,
    input enable,
    output reg [3:0] count
   );

   always @(posedge CLK) begin
      if (reset) begin
         count <= 4'b0;
      end else if (enable) begin
         count <= count + 1;
      end
   end

endmodule