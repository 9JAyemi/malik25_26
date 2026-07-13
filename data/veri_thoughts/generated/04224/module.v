module pipeline_register #(
  parameter n = 8 // width of the pipeline register
) (
  input clk,
  input rst,
  input [n-1:0] in,
  output reg [n-1:0] out
);

always @(posedge clk or posedge rst) begin
  if (rst) begin
    out <= 0;
  end else begin
    out <= in;
  end
end

endmodule