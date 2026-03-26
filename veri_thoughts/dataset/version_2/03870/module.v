module counter_4bit_async (
  input clk,
  input rst,
  input en,
  output reg [3:0] out
);

  always @(posedge clk or negedge rst) begin
    if (!rst) begin
      out <= 4'b0;
    end else if (en) begin
      out <= out + 1;
    end
  end

endmodule