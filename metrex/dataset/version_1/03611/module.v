
module PWM (
  input clk,
  input [7:0] in,
  output out
);

parameter clk_freq = 50000000; // 50 MHz
parameter pwm_freq = 1000; // 1 kHz

reg [31:0] counter = 0;
reg [7:0] threshold = 0;

assign out = (counter < threshold);

always @(posedge clk) begin
  counter <= counter + 1;
  if (counter >= (clk_freq / pwm_freq)) begin
    counter <= 0;
    threshold <= in;
  end
end

endmodule
