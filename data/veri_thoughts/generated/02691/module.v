
module adder_16bit(
    input [15:0] a,
    input [15:0] b,
    input sub,
    output [15:0] out
);

    assign out = sub ? a - b : a + b;

endmodule
module byte_reversal(
    input [31:0] in,
    output [31:0] out
);

    assign out = {in[7:0], in[15:8], in[23:16], in[31:24]};

endmodule
module bitwise_or(
    input [31:0] in1,
    input [31:0] in2,
    output [31:0] out
);

    assign out = in1 | in2;

endmodule
module top_module(
    input [31:0] a,
    input [31:0] b,
    input sub,
    input [31:0] in,
    output [31:0] out
);

    wire [15:0] adder_out;
    wire [31:0] byte_reversal_out;

    adder_16bit adder_inst(
        .a(a[15:0]),
        .b(b[15:0]),
        .sub(sub),
        .out(adder_out)
    );

    byte_reversal byte_reversal_inst(
        .in(in),
        .out(byte_reversal_out)
    );

    bitwise_or bitwise_or_inst(
        .in1({16'b0,adder_out}),
        .in2(byte_reversal_out),
        .out(out)
    );

endmodule