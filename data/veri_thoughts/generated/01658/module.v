module PWM (
  input clk,
  input [7:0] duty_cycle,
  output pwm_out
);

parameter resolution = 8; // number of steps in the duty cycle.

reg [7:0] duty_count;
reg pwm_out_reg;
wire [7:0] period_count;

assign period_count = (clk / 2) - 1;

always @(posedge clk) begin
  if (duty_count < duty_cycle) begin
    pwm_out_reg <= 1;
  end else begin
    pwm_out_reg <= 0;
  end
  
  duty_count <= duty_count + 1;
  
  if (duty_count == period_count) begin
    duty_count <= 0;
  end
end

assign pwm_out = pwm_out_reg;

endmodule