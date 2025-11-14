module top_module( 
    input [3:0] in,
    output out_and,
    output out_or,
    output out_xor
);

    wire [3:0] and_out;
    wire [3:0] or_out;
    wire [3:0] xor_out;

    and_module and_inst(
        .in1(in),
        .in2(in),
        .out(and_out)
    );

    or_module or_inst(
        .in1(in),
        .in2(in),
        .out(or_out)
    );

    xor_module xor_inst(
        .in1(in),
        .in2(in),
        .out(xor_out)
    );

    assign out_and = and_out[0] & and_out[1] & and_out[2] & and_out[3];
    assign out_or = or_out[0] | or_out[1] | or_out[2] | or_out[3];
    assign out_xor = xor_out[0] ^ xor_out[1] ^ xor_out[2] ^ xor_out[3];

endmodule

module and_module(
    input [3:0] in1,
    input [3:0] in2,
    output [3:0] out
);

    assign out = in1 & in2;

endmodule

module or_module(
    input [3:0] in1,
    input [3:0] in2,
    output [3:0] out
);

    assign out = in1 | in2;

endmodule

module xor_module(
    input [3:0] in1,
    input [3:0] in2,
    output [3:0] out
);

    assign out = in1 ^ in2;

endmodule