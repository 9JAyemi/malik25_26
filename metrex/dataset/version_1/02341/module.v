
module bitwise_or_logical_or(
    input [2:0] a,
    input [2:0] b,
    output [2:0] out_or_bitwise,
    output out_or_logical,
    output [5:0] out_not
);

    assign out_or_bitwise = a | b;
    assign out_or_logical = (a != 0) || (b != 0);
    assign out_not = ~{a, b};

endmodule
module and_or_xor(
    input [99:0] in,
    output out_and,
    output out_or,
    output out_xor
);

    wire [49:0] and_out;
    wire [49:0] or_out;
    wire [98:0] xor_out;

    genvar i;
    generate
        for (i = 0; i < 50; i = i + 1) 
            and_gate and_inst(
            .a(in[i*2]),
            .b(in[i*2+1]),
            .y(and_out[i])
        );

        for (i = 0; i < 50; i = i + 1) 
            or_gate or_inst(
            .a(in[i*2]),
            .b(in[i*2+1]),
            .y(or_out[i])
        );

        for (i = 0; i < 99; i = i + 1) 
            xor_gate xor_inst(
            .a(in[i]),
            .b(in[i+1]),
            .y(xor_out[i])
        );
    endgenerate

    assign out_and = &and_out;
    assign out_or = |or_out;
    assign out_xor = ^xor_out;

endmodule
module top_module( 
    input [2:0] a,
    input [2:0] b,
    output [2:0] out_or_bitwise,
    output out_or_logical,
    output [5:0] out_not,
    input [99:0] in,
    output out_and,
    output out_or,
    output out_xor,
    output [2:0] final_output
);

    bitwise_or_logical_or bitwise_or_logical_or_inst(
        .a(a),
        .b(b),
        .out_or_bitwise(out_or_bitwise),
        .out_or_logical(out_or_logical),
        .out_not(out_not)
    );

    and_or_xor and_or_xor_inst(
        .in(in),
        .out_and(out_and),
        .out_or(out_or),
        .out_xor(out_xor)
    );

    assign final_output = out_or_bitwise + out_or_bitwise;

endmodule
module and_gate(
    input a,
    input b,
    output y
);

    assign y = a & b;

endmodule
module or_gate(
    input a,
    input b,
    output y
);

    assign y = a | b;

endmodule
module xor_gate(
    input a,
    input b,
    output y
);

    assign y = a ^ b;

endmodule