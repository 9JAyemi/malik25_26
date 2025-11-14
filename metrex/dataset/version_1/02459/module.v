module Delay_Block (
  input in,
  output out,
  input clk // Clock signal
);

parameter delay = 2; // Amount of delay in number of clock cycles.

reg [delay-1:0] delay_reg; // Register to hold input signal for delay cycles

always @(posedge clk) begin
  delay_reg <= {delay_reg[delay-2:0], in}; // Shift input signal into register
end

assign out = delay_reg[delay-1]; // Output delayed signal

endmodule