
module LCB (
  input clk, // Clock input is necessary for synchronous design
  input [1:0] analog_signal, // Adjusted size for multiple case values
  input enable,
  input reset,
  output reg pwm_out
);

parameter pwm_width = 8; // width of the PWM signal
parameter pwm_frequency = 100; // frequency of the PWM signal

reg [pwm_width-1:0] pwm_counter;

always @(posedge clk or posedge reset) begin
  if (reset) begin
    pwm_counter <= 0;
  end else begin
    if (enable) begin
      pwm_counter <= pwm_counter + 1;
      if (pwm_counter >= (1 << pwm_width) - 1) // Ensure counter wraps around correctly
        pwm_counter <= 0;
    end
  end
end

reg [pwm_width-1:0] pwm_threshold;

always @(posedge clk or posedge reset) begin
  if (reset) begin
    pwm_threshold <= 0;
  end else begin
    case (analog_signal)
      2'b00: pwm_threshold <= pwm_width / 8;
      2'b01: pwm_threshold <= pwm_width / 4;
      2'b10: pwm_threshold <= pwm_width / 2;
      2'b11: pwm_threshold <= pwm_width - 1; // Ensure full scale is reachable
      default: pwm_threshold <= 0; // Safe default
    endcase
  end
end

always @(posedge clk or posedge reset) begin
  if (reset) begin
    pwm_out <= 0;
  end else begin
    if (enable) begin
      if (pwm_counter >= pwm_threshold) begin
        pwm_out <= 1;
      end else begin
        pwm_out <= 0;
      end
    end
  end
end

endmodule