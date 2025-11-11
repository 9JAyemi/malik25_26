module top_module (
    input [7:0] a,
    input [7:0] b,
    output [7:0] s,
    output overflow
);

    wire [7:0] c;
    wire [7:0] p;
    wire [7:0] g;
    wire [7:0] c_out;

    carry_lookahead_adder adder(
        .a(a),
        .b(b),
        .c_in(1'b0),
        .s(s),
        .c(c_out),
        .p(p),
        .g(g)
    );

    assign overflow = (a[7] == b[7]) && (a[7] != s[7]);

endmodule

module carry_lookahead_adder (
    input [7:0] a,
    input [7:0] b,
    input c_in,
    output [7:0] s,
    output [7:0] c,
    output [7:0] p,
    output [7:0] g
);

    wire [7:0] p0;
    wire [7:0] g0;
    wire [7:0] p1;
    wire [7:0] g1;
    wire [7:0] p2;
    wire [7:0] g2;
    wire [7:0] p3;
    wire [7:0] g3;
    wire [7:0] p4;
    wire [7:0] g4;
    wire [7:0] p5;
    wire [7:0] g5;
    wire [7:0] p6;
    wire [7:0] g6;
    wire [7:0] p7;
    wire [7:0] g7;

    assign p0 = a[0] ^ b[0];
    assign g0 = a[0] & b[0];
    assign p1 = a[1] ^ b[1] ^ g0;
    assign g1 = (a[1] & b[1]) | (g0 & (a[1] ^ b[1]));
    assign p2 = a[2] ^ b[2] ^ g1;
    assign g2 = (a[2] & b[2]) | (g1 & (a[2] ^ b[2]));
    assign p3 = a[3] ^ b[3] ^ g2;
    assign g3 = (a[3] & b[3]) | (g2 & (a[3] ^ b[3]));
    assign p4 = a[4] ^ b[4] ^ g3;
    assign g4 = (a[4] & b[4]) | (g3 & (a[4] ^ b[4]));
    assign p5 = a[5] ^ b[5] ^ g4;
    assign g5 = (a[5] & b[5]) | (g4 & (a[5] ^ b[5]));
    assign p6 = a[6] ^ b[6] ^ g5;
    assign g6 = (a[6] & b[6]) | (g5 & (a[6] ^ b[6]));
    assign p7 = a[7] ^ b[7] ^ g6;
    assign g7 = (a[7] & b[7]) | (g6 & (a[7] ^ b[7]));

    assign s = {p7, p6, p5, p4, p3, p2, p1, p0};
    assign c = {g7, g6, g5, g4, g3, g2, g1, g0};
    assign p = {p7, p6, p5, p4, p3, p2, p1, p0};
    assign g = {g7, g6, g5, g4, g3, g2, g1, g0, c_in};

endmodule