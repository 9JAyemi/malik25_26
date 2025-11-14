module carry_select_adder(
    input [31:0] a,
    input [31:0] b,
    output [31:0] sum
);

wire [31:0] c1, c2, p1, p2, g1, g2;

assign {c2, c1} = {b[31], a[31], 1'b0};
assign {g2, g1} = {b[31], a[31]};
assign {p2, p1} = {b[31]^1'b1, a[31]^1'b1};

wire [31:0] s1, s2, s3;

assign s1 = a + b;
assign s2 = s1 - {c1, p1};
assign s3 = s1 - {c2, p2};

assign sum = (g1 & g2) ? s3 : (g1 | g2) ? s2 : s1;

endmodule

module top_module(
    input [31:0] a,
    input [31:0] b,
    output [31:0] sum
);

carry_select_adder csa(.a(a), .b(b), .sum(sum));

endmodule