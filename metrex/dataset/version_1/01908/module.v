module carry_lookahead_adder (
    input [7:0] a,
    input [7:0] b,
    output [7:0] s,
    output carry_out
);

wire [7:0] p, g;
wire [7:0] c;

assign p = a ^ b;
assign g = a & b;

assign c[0] = g[0];
assign c[1] = g[1] | (p[1] & g[0]);
assign c[2] = g[2] | (p[2] & g[1]) | (p[2] & p[1] & g[0]);
assign c[3] = g[3] | (p[3] & g[2]) | (p[3] & p[2] & g[1]) | (p[3] & p[2] & p[1] & g[0]);
assign c[4] = g[4] | (p[4] & g[3]) | (p[4] & p[3] & g[2]) | (p[4] & p[3] & p[2] & g[1]) | (p[4] & p[3] & p[2] & p[1] & g[0]);
assign c[5] = g[5] | (p[5] & g[4]) | (p[5] & p[4] & g[3]) | (p[5] & p[4] & p[3] & g[2]) | (p[5] & p[4] & p[3] & p[2] & g[1]) | (p[5] & p[4] & p[3] & p[2] & p[1] & g[0]);
assign c[6] = g[6] | (p[6] & g[5]) | (p[6] & p[5] & g[4]) | (p[6] & p[5] & p[4] & g[3]) | (p[6] & p[5] & p[4] & p[3] & g[2]) | (p[6] & p[5] & p[4] & p[3] & p[2] & g[1]) | (p[6] & p[5] & p[4] & p[3] & p[2] & p[1] & g[0]);
assign c[7] = g[7] | (p[7] & g[6]) | (p[7] & p[6] & g[5]) | (p[7] & p[6] & p[5] & g[4]) | (p[7] & p[6] & p[5] & p[4] & g[3]) | (p[7] & p[6] & p[5] & p[4] & p[3] & g[2]) | (p[7] & p[6] & p[5] & p[4] & p[3] & p[2] & g[1]) | (p[7] & p[6] & p[5] & p[4] & p[3] & p[2] & p[1] & g[0]);

assign s = a + b + {1'b0, c};

assign carry_out = c[7];

endmodule

module overflow_detector (
    input [7:0] a,
    input [7:0] b,
    input [7:0] s,
    output overflow
);

assign overflow = ((a[7] == b[7]) && (a[7] != s[7]));

endmodule

module top_module (
    input [7:0] a,
    input [7:0] b,
    output [7:0] s,
    output overflow
);

carry_lookahead_adder adder(
    .a(a),
    .b(b),
    .s(s),
    .carry_out()
);

overflow_detector detector(
    .a(a),
    .b(b),
    .s(s),
    .overflow(overflow)
);

endmodule