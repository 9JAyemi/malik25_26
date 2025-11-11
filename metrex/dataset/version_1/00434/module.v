module DelayBlock (
  input in,
  input clk,
  output reg out
);

parameter delay = 5; // number of clock cycles

reg [delay-1:0] shift_reg = 0; // shift register to store input signal

always @(posedge clk) begin
  shift_reg <= {shift_reg[delay-2:0], in}; // shift input signal into shift register
end

always @* begin
  out <= shift_reg[0]; // output delayed signal
end

endmodule