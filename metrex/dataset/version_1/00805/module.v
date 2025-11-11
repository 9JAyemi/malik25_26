
module priority_encoder (
    input [7:0] in,
    output [2:0] pos
);

reg [2:0] pos_int;

always @* begin
    if (in[0]) pos_int = 0;
    else if (in[1]) pos_int = 1;
    else if (in[2]) pos_int = 2;
    else if (in[3]) pos_int = 3;
    else if (in[4]) pos_int = 4;
    else if (in[5]) pos_int = 5;
    else if (in[6]) pos_int = 6;
    else if (in[7]) pos_int = 7;
    else pos_int = 0;
end

assign pos = pos_int;

endmodule

module multiplexer (
    input [3:0] a, b, c, d,
    input [1:0] sel,
    output [3:0] y
);

wire [1:0] sel_inv;
assign sel_inv[0] = ~sel[0];
assign sel_inv[1] = ~sel[1];

wire [3:0] ab, cd;
assign ab = sel_inv[1] ? b : a;
assign cd = sel_inv[1] ? d : c;

wire [3:0] acd, bcd;
assign acd = sel_inv[0] ? ab : cd;
assign bcd = sel_inv[0] ? cd : ab;

assign y = sel[1] ? bcd : acd;

endmodule

module top_module (
    input [7:0] in,
    input [3:0] a, b, c, d,
    input [1:0] sel,
    output [2:0] pos,
    output [3:0] y
);

priority_encoder pe (
    .in(in),
    .pos(pos)
);

multiplexer mux (
    .a(a),
    .b(b),
    .c(c),
    .d(d),
    .sel(sel),
    .y(y)
);

endmodule
