
module crystal_oscillator_interface (
  input osc_in,
  input reset,
  input clk_enable,
  output reg clk_out
);

parameter osc_freq = 50000000; // frequency of the crystal oscillator
parameter clk_div = 2; // clock divider value

reg [31:0] counter;

always @ (posedge osc_in or posedge reset) begin
  if (reset) begin
    counter <= 0;
    clk_out <= 1'b0;
  end else begin
    counter <= counter + 1;
    if (counter == (osc_freq / (2 * clk_div))) begin
      counter <= 0;
      if (clk_enable) begin
        clk_out <= ~clk_out;
      end
    end
  end
end

endmodule