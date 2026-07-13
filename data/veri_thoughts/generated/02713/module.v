module and_gate (
    output reg [7:0] out,
    input [7:0] in1,
    input [7:0] in2
);

always @* begin
    out = in1 & in2;
end

endmodule

module or_gate (
    output reg [7:0] out,
    input [7:0] in1,
    input [7:0] in2
);

always @* begin
    out = in1 | in2;
end

endmodule

module three_to_one (
    input [7:0] A,
    input [7:0] B,
    input [7:0] C,
    output reg [7:0] X
);

wire [7:0] and_result;
wire [7:0] or_result;

and_gate and_gate_inst (
    .out(and_result),
    .in1(A),
    .in2(B)
);

or_gate or_gate_inst (
    .out(or_result),
    .in1(B),
    .in2(C)
);

always @* begin
    X = and_result ^ or_result;
end

endmodule