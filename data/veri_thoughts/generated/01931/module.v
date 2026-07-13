module and_gate_16bit(
    input [15:0] a,
    input [15:0] b,
    output [15:0] out
);

    assign out = a & b;

endmodule



module top_module(
    input [31:0] a,
    input [31:0] b,
    input op,
    output [31:0] result
);

    wire [15:0] and_out1, and_out2;

    and_gate_16bit and1(
        .a(a[15:0]),
        .b(b[15:0]),
        .out(and_out1)
    );

    and_gate_16bit and2(
        .a(a[31:16]),
        .b(b[31:16]),
        .out(and_out2)
    );

    wire [31:0] and_combined = {and_out2, and_out1};

    assign result = (op == 0) ? (a & b) : and_combined;

endmodule
