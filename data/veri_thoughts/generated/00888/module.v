
module pipelined_bitwise_operations(
    input [3:0] in1,
    input [3:0] in2,
    input [3:0] in3,
    input [3:0] in4,
    output [3:0] out_and,
    output [3:0] out_or,
    output [3:0] out_xor
);

reg [3:0] and1, and2, and3;
reg [3:0] or1, or2, or3;
reg [3:0] xor1, xor2, xor3;

always @(*) begin
    and1 = in1 & in2;
    or1 = in1 | in2;
    xor1 = in1 ^ in2;
    
    and2 = and1 & in3;
    or2 = or1 | in3;
    xor2 = xor1 ^ in3;
    
    and3 = and2 & in4;
    or3 = or2 | in4;
    xor3 = xor2 ^ in4;
end

assign out_and = and3;
assign out_or = or3;
assign out_xor = xor3;

endmodule

module top_module( 
    input [3:0] in1,
    input [3:0] in2,
    input [3:0] in3,
    input [3:0] in4,
    output [3:0] out_and,
    output [3:0] out_or,
    output [3:0] out_xor
);

pipelined_bitwise_operations pbo(
    .in1(in1),
    .in2(in2),
    .in3(in3),
    .in4(in4),
    .out_and(out_and),
    .out_or(out_or),
    .out_xor(out_xor)
);

endmodule
