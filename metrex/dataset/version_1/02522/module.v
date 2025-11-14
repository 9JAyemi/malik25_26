module AGC (
  input clk,
  input in,
  output out
);

parameter target_level = 100; // desired output signal level
parameter step_size = 1; // amount to adjust gain on each clock cycle

reg [7:0] gain = 128; // initial gain value
reg [15:0] sum = 0; // sum of input signal over time

always @(posedge clk) begin
  sum <= sum + in; // accumulate input signal over time
  if (sum > target_level) begin
    gain <= gain - step_size; // decrease gain
  end else if (sum < target_level) begin
    gain <= gain + step_size; // increase gain
  end
  sum <= 0; // reset sum for next cycle
end

assign out = in * gain; // compute output signal

endmodule