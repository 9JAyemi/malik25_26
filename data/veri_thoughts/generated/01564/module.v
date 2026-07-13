module counter(
  input clk,
  input reset,
  input [31:0] max_value,
  output reg [31:0] count
);

  always @(posedge clk) begin
    if (reset) begin
      count <= 0;
    end else if (count == max_value) begin
      count <= 0;
    end else begin
      count <= count + 1;
    end
  end

endmodule