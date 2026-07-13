
module adder (
    input [7:0] a,
    input [7:0] b,
    output [7:0] s,
    output carry_out
);

wire [7:0] sum1, sum2;
wire carry1, carry2;

assign {carry1, sum1} = a + b;
assign {carry2, sum2} = a + ~b + 1;

assign s = carry1 ? sum2 : sum1;
assign carry_out = carry1 ^ (a[7] ^ b[7]);

endmodule
module top_module (
    input [7:0] a,
    input [7:0] b,
    output [7:0] s,
    output overflow
);

wire [7:0] sum, sum1, sum2;
wire carry_out1, carry_out2;

adder adder1(
    .a(a),
    .b(b),
    .s(sum1),
    .carry_out(carry_out1)
);

adder adder2(
    .a(a),
    .b(~b + 1'b1),
    .s(sum2),
    .carry_out(carry_out2)
);

assign s = carry_out1 ? sum2 : sum1;
assign overflow = carry_out1 ^ carry_out2;

endmodule