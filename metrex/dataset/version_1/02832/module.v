module counter (
  input clk,
  input reset,
  output reg [3:0] count,
  output reg p,
  output reg q
);
  
  always @(posedge clk, posedge reset) begin
    if (reset) begin
      count <= 4'b0000;
    end else begin
      count <= count + 1;
    end
  end
  
  always @(count) begin
    p = ^count;
    q = &count;
  end
  
endmodule
