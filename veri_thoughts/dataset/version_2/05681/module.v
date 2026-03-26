
module binary_counter (
  input clk,
  input reset,
  output reg [15:0] count
);

  reg [15:0] count_reg;

  always @(posedge clk) begin
    if (reset) begin
      count_reg <= 16'b0000000000000000;
    end
    else begin
      count_reg <= count_reg + 1'b1;
    end
  end

  always @(*) begin
    count = count_reg;
  end

endmodule