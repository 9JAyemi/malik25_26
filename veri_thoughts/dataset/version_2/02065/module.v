module Freq_Divider#(
  parameter sys_clk = 50000000, // 50 MHz system clock
            clk_out = 1        // 1 Hz clock output
            )
  (Clk_in, Clk_out);

  // input ports
  input wire Clk_in;

  // output ports
  output reg Clk_out;

  // calculate the maximum counter size based on the input and output frequencies
  parameter max = sys_clk / (2*clk_out);

  // calculate the number of bits needed in the counter
  localparam N = $clog2(max);

  // counter
  reg [N-1:0] counter = 0;

  always @(posedge Clk_in) begin
    if (counter == max-1) begin
      counter <= 0;
      Clk_out <= ~Clk_out;
    end else begin
      counter <= counter + 1;
    end
  end

endmodule