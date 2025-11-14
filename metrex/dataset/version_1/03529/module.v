module async_reset_release (
  input rst,
  input clk,
  input enable,
  output reg rst_release
);

parameter delay_count = 10;

reg [7:0] delay_counter;

always @(posedge clk) begin
  if (rst) begin
    rst_release <= 0;
    delay_counter <= 0;
  end else if (enable) begin
    if (delay_counter < delay_count) begin
      delay_counter <= delay_counter + 1;
    end else begin
      rst_release <= 1;
    end
  end
end

endmodule