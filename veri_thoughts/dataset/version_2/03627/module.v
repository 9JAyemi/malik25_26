module top_module(
    input [4:0] in,
    input select,
    output out_and,
    output out_or,
    output out_nor
);

wire [3:0] decoder_out;
wire en_and, en_or, en_nor;

decoder_2to4_with_enable dec(
    .in(in[1:0]),
    .enable(select),
    .out(decoder_out)
);

and_gate_5input and_gate(
    .in(in),
    .enable(en_and),
    .out(out_and)
);

or_gate_5input or_gate(
    .in(in),
    .enable(en_or),
    .out(out_or)
);

nor_gate_5input nor_gate(
    .in(in),
    .enable(en_nor),
    .out(out_nor)
);

assign en_and = decoder_out[0];
assign en_or = decoder_out[1];
assign en_nor = decoder_out[2];

endmodule

module decoder_2to4_with_enable(
    input [1:0] in,
    input enable,
    output [3:0] out
);

wire [3:0] dec_out;

decoder_2to4 dec(
    .in(in),
    .out(dec_out)
);

assign out = enable ? dec_out : 4'b0000;

endmodule

module decoder_2to4(
    input [1:0] in,
    output [3:0] out
);

assign out = 4'b0001 << in;

endmodule

module and_gate_5input(
    input [4:0] in,
    input enable,
    output out
);

assign out = enable ? (in[0] & in[1] & in[2] & in[3] & in[4]) : 1'b0;

endmodule

module or_gate_5input(
    input [4:0] in,
    input enable,
    output out
);

assign out = enable ? (in[0] | in[1] | in[2] | in[3] | in[4]) : 1'b0;

endmodule

module nor_gate_5input(
    input [4:0] in,
    input enable,
    output out
);

wire or_out;

or_gate_5input or_gate(
    .in(in),
    .enable(enable),
    .out(or_out)
);

assign out = ~or_out;

endmodule