module and_module(
    input [7:0] in1,
    input [7:0] in2,
    output [7:0] out
);
    assign out = in1 & in2;
endmodule

module xor_module(
    input [7:0] in1,
    input [7:0] in2,
    output [7:0] out
);
    assign out = in1 ^ in2;
endmodule

module final_module(
    input [7:0] and_out,
    input [7:0] xor_out,
    input select,
    output [7:0] out
);
    assign out = select ? xor_out : and_out;
endmodule

module top_module( 
    input clk,
    input reset,
    input [7:0] in1,
    input [7:0] in2,
    input select,
    output [7:0] out
);
    wire [7:0] and_out;
    wire [7:0] xor_out;

    and_module and_inst(
        .in1(in1),
        .in2(in2),
        .out(and_out)
    );

    xor_module xor_inst(
        .in1(and_out),
        .in2(in2),
        .out(xor_out)
    );

    final_module final_inst(
        .and_out(and_out),
        .xor_out(xor_out),
        .select(select),
        .out(out)
    );
endmodule