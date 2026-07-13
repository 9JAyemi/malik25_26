module full_adder(
    input a,
    input b,
    input c_in,
    output sum,
    output c_out
);

    assign {c_out, sum} = a + b + c_in;

endmodule

module combinational_circuit(
    input [3:0] in,
    output out_and,
    output out_or,
    output out_xor
);

    assign out_and = in[0] & in[1] & in[2] & in[3];
    assign out_or = in[0] | in[1] | in[2] | in[3];
    assign out_xor = in[0] ^ in[1] ^ in[2] ^ in[3];

endmodule

module functional_module(
    input a, b, c_in,
    input [3:0] in,
    output c_out,
    output sum,
    output out_and,
    output out_or,
    output out_xor
);

    wire full_adder_sum;
    wire full_adder_c_out;

    combinational_circuit cc(
        .in(in),
        .out_and(out_and),
        .out_or(out_or),
        .out_xor(out_xor)
    );

    full_adder fa(
        .a(a),
        .b(b),
        .c_in(c_in),
        .sum(full_adder_sum),
        .c_out(full_adder_c_out)
    );

    assign sum = full_adder_sum;

    assign c_out = (full_adder_sum & out_xor) ? 1'b0 : full_adder_c_out;

endmodule