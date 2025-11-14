module binary_counter (
  input clk,
  input rst,
  input [15:0] max_count,
  output reg [15:0] count
);

  always @(posedge clk) begin
    if (rst) begin
      count <= 16'b0000000000000000;
    end else if (count == max_count) begin
      count <= 16'b0000000000000000;
    end else begin
      count <= count + 1;
    end
  end

endmodule