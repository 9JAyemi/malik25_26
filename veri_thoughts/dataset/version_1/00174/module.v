
module adder16 (
   input clk,
   input rst,
   input [15:0] A,
   input [15:0] B,
   output reg [15:0] Z
);

   always @(posedge clk) begin
      if (rst) begin
         Z <= 16'h0000;
      end else begin
         Z <= A + B;
      end
   end

endmodule