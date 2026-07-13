
module carry_select_adder(
    input [99:0] a, b,
    input cin,
    output cout,
    output [99:0] sum
);

wire [99:0] p, g, c, s;
wire [49:0] c0, c1, c2, c3, c4, c5, c6, c7, c8, c9;

assign p = a ^ b;
assign g = a & b;
assign c0 = cin;
assign c1 = g[0] | (p[0] & c0);
assign c2 = g[1] | (p[1] & c1);
assign c3 = g[2] | (p[2] & c2);
assign c4 = g[3] | (p[3] & c3);
assign c5 = g[4] | (p[4] & c4);
assign c6 = g[5] | (p[5] & c5);
assign c7 = g[6] | (p[6] & c6);
assign c8 = g[7] | (p[7] & c7);
assign c9 = g[8] | (p[8] & c8);

assign s = p ^ c;
assign cout = c9;
assign sum = cout ? b : a;

endmodule
module top_module( 
    input [99:0] a, b,
    input cin,
    output cout,
    output [99:0] sum );

carry_select_adder csa(
    .a(a),
    .b(b),
    .cin(cin),
    .cout(cout),
    .sum(sum)
);

endmodule