module counter(
   input clk,
   output reg [3:0] out
);

always @(posedge clk) begin
   if (out == 4'b1111) begin
      out <= 4'b0000;
   end
   else begin
      out <= out + 1;
   end
end

endmodule