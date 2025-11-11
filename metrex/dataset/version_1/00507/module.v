module watchdog_timer (
  input clk,
  input reset,
  input [31:0] timeout,
  output wd_reset
);

  reg [31:0] counter;
  reg wd_reset_reg;

  always @(posedge clk or posedge reset) begin
    if (reset) begin
      counter <= 0;
      wd_reset_reg <= 0;
    end
    else begin
      counter <= counter + 1;
      if (counter == timeout) begin
        wd_reset_reg <= 1;
      end
      else begin
        wd_reset_reg <= 0;
      end
    end
  end

  assign wd_reset = wd_reset_reg;

endmodule