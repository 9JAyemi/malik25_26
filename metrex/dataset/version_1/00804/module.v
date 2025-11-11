
module delay_block (
  input clk,
  input in,
  output reg out
);

parameter delay = 10; // delay time in nanoseconds

reg [31:0] count = 0; // 32-bit counter to count up to the specified delay time
reg delayed_in = 0; // delayed input signal

always @(posedge clk) begin
  if (in != delayed_in) begin // reset the counter whenever the input signal changes
    count <= 0;
    delayed_in <= in;
  end else if (count < delay) begin // increment the counter until it reaches the delay time
    count <= count + 1;
  end else begin // output the delayed input signal
    out <= delayed_in;
  end
end

endmodule
