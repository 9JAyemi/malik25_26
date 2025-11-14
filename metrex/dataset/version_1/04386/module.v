
module top_module(
    input a,
    input b,
    input c,
    output w,
    output x,
    output y,
    output z
);

    wire nor_out;
    wire [3:0] decoder_out;
    wire final_out;

    nor_gate nor_inst(
        .a(a),
        .b(b),
        .nor_out(nor_out)
    );

    decoder_3_4 decoder_inst(
        .a(a),
        .b(b),
        .c(c),
        .w(decoder_out[0]),
        .x(decoder_out[1]),
        .y(decoder_out[2]),
        .z(decoder_out[3])
    );

    functional_module func_inst(
        .nor_out(nor_out),
        .decoder_out(decoder_out),
        .final_out(final_out)
    );

    assign w = decoder_out[0];
    assign x = decoder_out[1];
    assign y = decoder_out[2];
    assign z = decoder_out[3];

endmodule

module nor_gate(
    input a,
    input b,
    output nor_out
);

    assign nor_out = !(a & b);

endmodule

module decoder_3_4(
    input a,
    input b,
    input c,
    output w,
    output x,
    output y,
    output z
);

    assign w = ~(a | b | c);
    assign x = ~(a | b | ~c);
    assign y = ~(a | ~b | c);
    assign z = ~(a | ~b | ~c);

endmodule

module functional_module(
    input nor_out,
    input [3:0] decoder_out,
    output final_out
);

    assign final_out = nor_out & decoder_out;

endmodule
