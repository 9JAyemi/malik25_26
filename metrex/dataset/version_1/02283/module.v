
module ripple_carry_adder(
    input [1:0] a,
    input [1:0] b,
    input cin,
    output [1:0] sum,
    output cout
);

assign {cout, sum} = a + b + cin;

endmodule
module detect_carry_adder(
    input [1:0] a,
    input [1:0] b,
    input cin,
    output p,
    output g
);

assign p = a & b;
assign g = a | b;

endmodule
module GDA_St_N8_M4_P2(
    input [7:0] in1,
    input [7:0] in2,
    output [7:0] res
);

wire [1:0] temp1, temp2, temp3, temp4;
wire g0, g1, g2, g3, g4, g5;
wire p0, p1, p2, p3, p4, p5;
wire p1g0, p3g2, p5g4;
wire c2, c4, c6;

ripple_carry_adder rca_0(.a(in1[1:0]), .b(in2[1:0]), .cin(1'b0), .sum(temp1), .cout(c2));
ripple_carry_adder rca_1(.a(in1[3:2]), .b(in2[3:2]), .cin(c2), .sum(temp2), .cout(c4));
ripple_carry_adder rca_2(.a(in1[5:4]), .b(in2[5:4]), .cin(c4), .sum(temp3), .cout(c6));
ripple_carry_adder rca_3(.a(in1[7:6]), .b(in2[7:6]), .cin(c6), .sum(temp4), .cout());

detect_carry_adder dca_0(.a(in1[1:0]), .b(in2[1:0]), .cin(1'b0), .p(p0), .g(g0));
detect_carry_adder dca_1(.a(in1[1:0]), .b(in2[1:0]), .cin(p1g0), .p(p1), .g(g1));
detect_carry_adder dca_2(.a(in1[3:2]), .b(in2[3:2]), .cin(p1g0), .p(p2), .g(g2));
detect_carry_adder dca_3(.a(in1[3:2]), .b(in2[3:2]), .cin(p3g2), .p(p3), .g(g3));
detect_carry_adder dca_4(.a(in1[5:4]), .b(in2[5:4]), .cin(p3g2), .p(p4), .g(g4));
detect_carry_adder dca_5(.a(in1[5:4]), .b(in2[5:4]), .cin(p5g4), .p(p5), .g(g5));

assign p1g0 = p1 & g0;
assign p3g2 = p3 & g2;
assign p5g4 = p5 & g4;

assign res[1:0] = temp1;
assign res[3:2] = temp2;
assign res[5:4] = temp3;
assign res[7:6] = temp4;

endmodule