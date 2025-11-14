module carry_lookahead_adder(
    input [15:0] a,
    input [15:0] b,
    input cin,
    output [15:0] sum,
    output cout
);

wire [3:0] g;
wire [3:0] p;
wire [3:0] c;

assign g[0] = a[0] & b[0];
assign p[0] = a[0] | b[0];
assign c[0] = cin;

assign g[1] = a[1] & b[1];
assign p[1] = a[1] | b[1];
assign c[1] = g[0] | (p[0] & cin);

assign g[2] = a[2] & b[2];
assign p[2] = a[2] | b[2];
assign c[2] = g[1] | (p[1] & g[0]) | (p[1] & p[0] & cin);

assign g[3] = a[3] & b[3];
assign p[3] = a[3] | b[3];
assign c[3] = g[2] | (p[2] & g[1]) | (p[2] & p[1] & g[0]) | (p[2] & p[1] & p[0] & cin);

assign sum = {c[3], c[2], c[1], c[0], a[15:4] + b[15:4] + c[3:0]};
assign cout = c[3];

endmodule

module top_module(
    input [31:0] a,
    input [31:0] b,
    output [31:0] sum
);

wire [15:0] a_low = a[15:0];
wire [15:0] b_low = b[15:0];
wire [15:0] a_high = a[31:16];
wire [15:0] b_high = b[31:16];
wire cin;

carry_lookahead_adder adder_low(.a(a_low), .b(b_low), .cin(1'b0), .sum(sum[15:0]), .cout(cin));
carry_lookahead_adder adder_high(.a(a_high), .b(b_high), .cin(cin), .sum(sum[31:16]), .cout());

endmodule