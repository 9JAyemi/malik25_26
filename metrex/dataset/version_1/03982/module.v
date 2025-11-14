
module mul_bodec_multiplier(a_reg, b_reg, p_high, p_low);

input [15:0] a_reg, b_reg;
output [15:0] p_high, p_low;

wire [2:0] b0, b1, b2, b3, b4, b5, b6, b7;
wire [31:0] p;

mul_bodec_16bit mul_bodec_inst (
  .x(a_reg[0]),
  .b(b_reg),
  .b0(b0),
  .b1(b1),
  .b2(b2),
  .b3(b3),
  .b4(b4),
  .b5(b5),
  .b6(b6),
  .b7(b7)
);

assign p[31:16] = {16'b0, b4, b5, b6, b7};
assign p[15:0] = {b0, b1, b2, b3, 5'b0};

assign p_high = p[31:16];
assign p_low = p[15:0];

endmodule

module mul_bodec_16bit(x, b, b0, b1, b2, b3, b4, b5, b6, b7);

input x;
input [15:0] b;
output [2:0] b0, b1, b2, b3, b4, b5, b6, b7;

assign b0 = x ? b[ 2: 0] : 3'b0;
assign b1 = x ? b[ 5: 3] : 3'b0;
assign b2 = x ? b[ 8: 6] : 3'b0;
assign b3 = x ? b[11: 9] : 3'b0;
assign b4 = x ? b[14:12] : 3'b0;
assign b5 = x ? b[15]    : 1'b0;
assign b6 = 3'b0;
assign b7 = 3'b0;

endmodule
