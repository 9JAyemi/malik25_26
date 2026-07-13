
module and_or_xor(
    input [3:0] a,
    input [3:0] b,
    input select,
    output [3:0] and_out,
    output [3:0] or_out,
    output [3:0] xor_out
);

    and_or_xor_4_input and_or_xor_4_input_inst(.a(a), .b(b), .and_out(and_out), .or_out(or_out), .xor_out(xor_out));

endmodule

module and_or_xor_4_input(
    input [3:0] a,
    input [3:0] b,
    output [3:0] and_out,
    output [3:0] or_out,
    output [3:0] xor_out
);

    assign and_out = a & b;
    assign or_out = a | b;
    assign xor_out = a ^ b;

endmodule

module top_module(
    input [99:0] in,
    output [3:0] and_out,
    output [3:0] or_out,
    output [3:0] xor_out
);

    and_or_xor and_or_xor_inst(.a(in[3:0]), .b(in[7:4]), .and_out(and_out), .or_out(or_out), .xor_out(xor_out));

endmodule
