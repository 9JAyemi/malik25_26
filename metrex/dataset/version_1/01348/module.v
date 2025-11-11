
module clock_divider (
  input clock,
  input reset,
  output reg clk_out
);

parameter divisor = 2; // factor by which the frequency of the input clock signal is divided

always @ (posedge clock, posedge reset) begin
  if (reset) begin
    clk_out <= 0;
    counter <= 0;
  end else begin
    if (counter == divisor - 1) begin
      clk_out <= ~clk_out;
      counter <= 0;
    end else begin
      counter <= counter + 1;
    end
  end
end

reg [32-1:0] counter;

endmodule
