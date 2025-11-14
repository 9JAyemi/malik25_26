module counter #(
  parameter n = 4 // number of bits in the counter
) (
  input clk,
  input rst,
  output reg [n-1:0] count
);

always @(posedge clk or posedge rst) begin
  if (rst) begin
    count <= 0;
  end else begin
    count <= count + 1;
  end
end


endmodule