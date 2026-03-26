module binary_counter(clk, rst, count);
  input clk, rst;
  output reg [3:0] count;
  
  always @(posedge clk) begin
    if(rst) begin
      count <= 4'b0000;
    end else if(count == 4'b1111) begin
      count <= 4'b0000;
    end else begin
      count <= count + 1;
    end
  end
endmodule