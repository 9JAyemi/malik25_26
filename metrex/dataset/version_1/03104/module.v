module motor_controller (
  input clk,
  input [7:0] pwm_width,
  input dir,
  output pwm,
  output hbridge_out1,
  output hbridge_out2
);

parameter pwm_freq = 100000; // PWM frequency in Hz
parameter max_pwm_width = 255; // maximum PWM width
parameter hbridge_deadband = 10; // deadband time for the H-bridge circuit in ns

reg [7:0] pwm_counter;
reg pwm_out;
reg hbridge_dir;

always @(posedge clk) begin
  // PWM counter
  if (pwm_counter == max_pwm_width) begin
    pwm_counter <= 0;
    pwm_out <= 0;
  end else if (pwm_counter < pwm_width) begin
    pwm_counter <= pwm_counter + 1;
    pwm_out <= 1;
  end else begin
    pwm_counter <= pwm_counter + 1;
    pwm_out <= 0;
  end
  
  // H-bridge direction
  if (dir == 0) begin
    hbridge_dir <= 1;
  end else begin
    hbridge_dir <= 0;
  end
end

assign pwm = pwm_out;
assign hbridge_out1 = hbridge_dir;
assign hbridge_out2 = ~hbridge_dir;

endmodule