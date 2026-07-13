
module counter(clk, reset, count);
  input clk, reset;
  output reg [1:0] count;
  
  always @(posedge clk) begin
    if (reset) begin
      count <= 2'b0;
    end else if (count == 2'b11) begin
      count <= 2'b0;
    end else begin
      count <= count + 1;
    end
  end
endmodule