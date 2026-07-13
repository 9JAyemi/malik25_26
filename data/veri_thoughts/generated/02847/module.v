module d_flip_flop (
    input clk,
    input d,
    output q
);

reg q_reg;

always @(negedge clk) begin
    q_reg <= d;
end

assign q = q_reg;

endmodule

module eight_d_flip_flops (
    input clk,
    input [7:0] d,
    output [7:0] q
);

reg [7:0] shift_reg;

always @(negedge clk) begin
    shift_reg <= {shift_reg[6:0], d};
end

d_flip_flop flipflop0 (.clk(clk), .d(shift_reg[0]), .q(q[0]));
d_flip_flop flipflop1 (.clk(clk), .d(shift_reg[1]), .q(q[1]));
d_flip_flop flipflop2 (.clk(clk), .d(shift_reg[2]), .q(q[2]));
d_flip_flop flipflop3 (.clk(clk), .d(shift_reg[3]), .q(q[3]));
d_flip_flop flipflop4 (.clk(clk), .d(shift_reg[4]), .q(q[4]));
d_flip_flop flipflop5 (.clk(clk), .d(shift_reg[5]), .q(q[5]));
d_flip_flop flipflop6 (.clk(clk), .d(shift_reg[6]), .q(q[6]));
d_flip_flop flipflop7 (.clk(clk), .d(shift_reg[7]), .q(q[7]));

endmodule

module top_module (
    input clk,
    input [7:0] d,
    output [7:0] q
);

eight_d_flip_flops flipflops (.clk(clk), .d(d), .q(q));

endmodule