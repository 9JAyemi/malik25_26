module bitwise_op(
    input [99:0] in1,
    input [99:0] in2,
    output [99:0] out_or,
    output [99:0] out_xor
);

    assign out_or = in1 | in2;
    assign out_xor = in1 ^ in2;

endmodule

module top_module( 
    input [99:0] in1,
    input [99:0] in2,
    output [99:0] out_and
);

    wire [99:0] wire1;
    wire [99:0] wire2;
    wire [99:0] wire3;

    bitwise_op op1(
        .in1(in1),
        .in2(in2),
        .out_or(wire1),
        .out_xor(wire2)
    );

    bitwise_op op2(
        .in1(wire1),
        .in2(wire2),
        .out_or(wire3),
        .out_xor(out_and)
    );

endmodule