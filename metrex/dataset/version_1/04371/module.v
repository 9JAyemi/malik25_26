module async_reset_release (
  input reset,
  input clk,
  output rst
);

  reg [3:0] counter;
  reg rst_active;

  always @(posedge clk or negedge reset) begin
    if (!reset) begin
      counter <= 0;
      rst_active <= 1'b1;
    end else begin
      if (counter == 4'd10) begin
        rst_active <= 1'b0;
      end else begin
        counter <= counter + 1;
      end
    end
  end

  assign rst = rst_active;

endmodule