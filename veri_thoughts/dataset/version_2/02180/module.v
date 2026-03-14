module xor_module(
    input [99:0] in1,
    input [99:0] in2,
    output [99:0] out_xor
);
    assign out_xor = in1 ^ in2;
endmodule

module and_module(
    input [99:0] in1,
    input [99:0] in2,
    output [99:0] out_and
);
    assign out_and = in1 & in2;
endmodule

module functional_module(
    input [99:0] in_xor,
    input [99:0] in_and,
    output [199:0] out_func
);
    assign out_func = {in_xor, in_and};
endmodule

module top_module( 
    input [99:0] in1,
    input [99:0] in2,
    output [99:0] out_xor,
    output [99:0] out_and,
    output [199:0] out_func
);

    xor_module xor_inst(
        .in1(in1),
        .in2(in2),
        .out_xor(out_xor)
    );

    and_module and_inst(
        .in1(in1),
        .in2(in2),
        .out_and(out_and)
    );

    functional_module func_inst(
        .in_xor(out_xor),
        .in_and(out_and),
        .out_func(out_func)
    );

endmodule