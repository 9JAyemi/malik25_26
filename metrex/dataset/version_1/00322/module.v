
module glitch_filter (
  input clk,
  input in,
  output reg out
);

parameter p = 5; // number of clock cycles for the delay line
parameter q = 2; // number of clock cycles for the glitch filter

reg [p-1:0] delay_line; // shift register for delay line

always @(posedge clk) begin
  delay_line <= {delay_line[p-2:0], in}; // shift input into delay line
  if (in != delay_line[p-1]) begin
    out <= delay_line[p-1]; // output delayed input signal
  end
  if (in != delay_line[p-1] && in == delay_line[p-q-1]) begin
    out <= delay_line[p-2]; // remove glitch by setting output to previous value
  end
end

endmodule