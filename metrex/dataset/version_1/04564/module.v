module watchdog_timer (
  input clk,
  input rst,
  input [31:0] timeout,
  output reg t
);

  reg [31:0] counter;

  always @(posedge clk) begin
    if (rst) begin
      counter <= 0;
      t <= 0;
    end
    else begin
      counter <= counter + 1;
      if (counter == timeout) begin
        t <= 1;
      end
      else begin
        t <= 0;
      end
    end
  end

endmodule