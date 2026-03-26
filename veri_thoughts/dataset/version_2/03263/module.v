
module xor_gate (
    input wire a,
    input wire b,
    output wire  out
);

    assign out = a ^ b;

endmodule
module byte_reversal (
    input wire [31:0] in,
    output wire  [31:0] out
);

    assign out = {in[7:0], in[15:8], in[23:16], in[31:24]};

endmodule
module functional_module (
    input wire  in1,
    input wire [31:0] in2,
    output wire  [31:0] out
);

    assign out = {31'b0, in1} | in2;

endmodule
module top_module (
    input wire a,
    input wire b,
    input wire [31:0] in,
    input wire select,
    output wire [31:0] out
);

    wire out_xor;
    wire [31:0] byte_rev_out;
    wire [31:0] func_out;

    xor_gate xor_inst (
        .a(a),
        .b(b),
        .out(out_xor)
    );

    byte_reversal byte_rev_inst (
        .in(in),
        .out(byte_rev_out)
    );

    functional_module func_inst (
        .in1(out_xor),
        .in2(byte_rev_out),
        .out(func_out)
    );

    assign out = (select) ? func_out : {31'b0, out_xor};

endmodule