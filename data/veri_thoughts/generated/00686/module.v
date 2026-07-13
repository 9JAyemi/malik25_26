module binary_to_gray_converter (
  input clk,
  input areset,
  input [3:0] bin,
  output reg [3:0] gray
);

  always @(posedge clk or negedge areset) begin
    if (!areset) begin
      gray <= 4'b0000;
    end else begin
      gray <= bin ^ (bin >> 1);
    end
  end
  
endmodule
