module PWM (
  input clk,
  input ref,
  input [7:0] duty,
  output reg pwm
);

parameter width = 8; // width of PWM output signal
parameter period = 256; // period of PWM output signal

reg [7:0] count;
reg [7:0] threshold;

always @(posedge clk) begin
  count <= count + 1;
  if (count == period - 1) begin
    count <= 0;
  end
end

always @(*) begin
  threshold = (duty * period) / 256;
end

always @(posedge clk) begin
  if (count < threshold) begin
    pwm <= 1;
  end else begin
    pwm <= 0;
  end
end

endmodule