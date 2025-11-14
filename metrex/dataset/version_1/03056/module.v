
module PWM (
  input clk,
  input [7:0] ctrl,
  input [15:0] period,
  output reg pwm_out
);

  reg [15:0] count;
  reg [7:0] duty_cycle;

  always @(posedge clk) begin
    count <= count + 1;
    if (count >= period) begin
      count <= 0;
    end
    pwm_out <= (count < duty_cycle);
  end

  always @(posedge clk) begin
    duty_cycle <= ctrl;
  end

endmodule
