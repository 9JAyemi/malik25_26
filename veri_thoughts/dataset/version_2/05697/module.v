module ClockBufferDriver #(
  parameter n = 4 // number of output clock signals
) (
  input clk,
  output [n-1:0] clk_out
);


reg [n-1:0] clk_buf;

always @(posedge clk) begin
  clk_buf <= {clk_buf[n-2:0], clk_buf[n-1]};
end

assign clk_out = clk_buf;

endmodule