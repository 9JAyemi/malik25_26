
module top_module(
    input [3:0] in,
    input [2:0] a,
    input [2:0] b,
    input [1:0] select,
    output [1:0] pos,
    output [2:0] out_or_bitwise,
    output out_or_logical,
    output [5:0] out_not,
    output [2:0] out
);
    functional_module fm(.in(in), .a(a), .b(b), .select(select), .pos(pos), .out_or_bitwise(out_or_bitwise), .out_or_logical(out_or_logical), .out_not(out_not), .out(out));
endmodule

module functional_module(
    input [3:0] in,
    input [2:0] a,
    input [2:0] b,
    input [1:0] select, // Added the select input port
    output [1:0] pos,
    output [2:0] out_or_bitwise,
    output out_or_logical,
    output [5:0] out_not,
    output [2:0] out
);
    priority_encoder pe(.in(in), .pos(pos));
    binary_module bm(.a(a), .b(b), .out_or_bitwise(out_or_bitwise), .out_or_logical(out_or_logical), .out_not(out_not));
    assign out = (select == 0) ? pos :
                 (select == 1) ? {out_or_bitwise, out_or_logical, out_not[5:3]} :
                                 {out_or_bitwise & out_not[2:0], out_or_logical & out_not[2:0]};
endmodule

module priority_encoder(
    input [3:0] in,
    output [1:0] pos
);
    assign pos = (in[3]) ? 2'b11 :
                 (in[2]) ? 2'b10 :
                 (in[1]) ? 2'b01 :
                 (in[0]) ? 2'b00 :
                           2'b00 ;
endmodule

module binary_module(
    input [2:0] a,
    input [2:0] b,
    output [2:0] out_or_bitwise,
    output out_or_logical,
    output [5:0] out_not
);
    assign out_or_bitwise = a | b;
    assign out_or_logical = (a || b);
    assign out_not = ~{a, b};
endmodule
