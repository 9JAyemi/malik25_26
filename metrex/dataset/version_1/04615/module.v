
module Shift_Register (
  input [n-1:0] in,
  input ctrl,
  output [m-1:0] out
);

parameter n = 4; // number of input signals
parameter m = 4; // number of output signals
parameter w = 8; // width of the shift register (i.e., the number of flip-flops)

reg [w-1:0] shift_reg;

always @(posedge ctrl) begin
  shift_reg <= {shift_reg[w-1:m], in};
end

assign out = shift_reg[m-1:0];

endmodule
