module BusHold #(
  parameter n = 8
) (
  input [n-1:0] in,
  input clk,
  input rst,
  output [n-1:0] out
);


reg [n-1:0] hold; // register to hold the data on the bus

always @(posedge clk) begin
  if (rst) begin
    hold <= 0; // reset the register to 0
  end else begin
    hold <= in; // latch the input signals on the rising edge of the clock
  end
end

assign out = hold; // assign the output signals to the register

endmodule