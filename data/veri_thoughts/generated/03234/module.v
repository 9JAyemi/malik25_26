
module toggle_output (
  input clk,
  output reg out
);

  reg [31:0] count = 0; // 32-bit counter
  reg clk_divider = 0; // clock divider

  always @ (posedge clk_divider) begin
    count <= count + 1; // increment counter
    if (count == 50000000) begin // toggle output every second
      out <= ~out;
      count <= 0;
    end
  end

  always @ (posedge clk) begin
    clk_divider <= ~clk_divider; // divide clock by 2
  end

endmodule
