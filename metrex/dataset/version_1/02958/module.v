
module BOR (
  input wire vcc,
  input wire clk,
  output reg rst,
  input wire vth // voltage threshold
);

parameter vcc_min = 1.2; // minimum voltage level of power supply
parameter t_reset = 10; // duration of reset signal in clock cycles. 

reg [7:0] counter; // 8-bit counter to keep track of reset duration

always @(posedge clk) begin
  if (vcc < vth) begin
    rst <= 1'b1; // assert reset signal if voltage is below threshold
    counter <= counter + 1; // increment counter
  end else begin
    if (counter >= t_reset) begin
      rst <= 1'b0; // de-assert reset signal if duration is over
      counter <= 8'd0; // reset counter
    end else begin
      counter <= counter + 1; // increment counter
    end
  end
end

endmodule