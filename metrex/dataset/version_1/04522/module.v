module watchdog_timer (
  input clk,
  input rst,
  input [7:0] time,
  output wdt
);

  reg [7:0] timer;
  reg wdt_enable;

  always @(posedge clk) begin
    if (rst) begin
      timer <= time;
      wdt_enable <= 0;
    end else begin
      if (timer == 0) begin
        wdt_enable <= 1;
      end else if (wdt_enable && timer > 0) begin
        timer <= timer - 1;
      end
    end
  end

  assign wdt = wdt_enable;

endmodule