module xor_gate(
    input wire a,
    input wire b,
    output wire out
);

    assign out = a ^ b;

endmodule

module half_word_splitter(
    input wire [15:0] in,
    input wire sel,
    output wire [7:0] out_hi,
    output wire [7:0] out_lo
);

    assign out_hi = (sel == 1'b0) ? in[15:8] : in[7:0];
    assign out_lo = (sel == 1'b0) ? in[7:0] : in[15:8];

endmodule

module xor_splitter(
    input wire [15:0] in,
    input wire a,
    input wire b,
    output wire [7:0] out_hi,
    output wire [7:0] out_lo,
    output wire [7:0] out_xor
);

    wire xor_out;
    xor_gate xor_inst(
        .a(a),
        .b(b),
        .out(xor_out)
    );

    half_word_splitter splitter_inst(
        .in(in),
        .sel(xor_out),
        .out_hi(out_hi),
        .out_lo(out_lo)
    );

    assign out_xor = out_hi ^ out_lo;

endmodule

module top_module(
    input wire [15:0] in,
    input wire a,
    input wire b,
    output wire [7:0] out_hi,
    output wire [7:0] out_lo,
    output wire [7:0] out_xor
);

    xor_splitter xor_splitter_inst(
        .in(in),
        .a(a),
        .b(b),
        .out_hi(out_hi),
        .out_lo(out_lo),
        .out_xor(out_xor)
    );

endmodule