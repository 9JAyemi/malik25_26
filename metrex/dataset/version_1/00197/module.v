module top_module(
    input [3:0] in0,
    input [3:0] in1,
    input [3:0] in2,
    input [3:0] in3,
    input [1:0] sel,
    output [3:0] out
);

wire [3:0] mux_out;
wire [3:0] adder_out;

mux_4to1 mux(
    .in0(in0),
    .in1(in1),
    .in2(in2),
    .in3(in3),
    .sel(sel),
    .out(mux_out)
);

binary_adder adder(
    .a(mux_out),
    .b(4'b0011),
    .sum(adder_out)
);

assign out = adder_out;

endmodule

module mux_4to1(
    input [3:0] in0,
    input [3:0] in1,
    input [3:0] in2,
    input [3:0] in3,
    input [1:0] sel,
    output [3:0] out
);

wire [3:0] and0_out;
wire [3:0] and1_out;
wire [3:0] and2_out;
wire [3:0] and3_out;
wire [3:0] or0_out;
wire [3:0] or1_out;

assign and0_out = sel[1] & sel[0] ? in3 : 4'b0000;
assign and1_out = sel[1] & ~sel[0] ? in2 : 4'b0000;
assign and2_out = ~sel[1] & sel[0] ? in1 : 4'b0000;
assign and3_out = ~sel[1] & ~sel[0] ? in0 : 4'b0000;

assign or0_out = and0_out | and1_out;
assign or1_out = and2_out | and3_out;

assign out = or0_out | or1_out;

endmodule

module binary_adder(
    input [3:0] a,
    input [3:0] b,
    output reg [3:0] sum
);

always @* begin
    sum = a + b;
end

endmodule