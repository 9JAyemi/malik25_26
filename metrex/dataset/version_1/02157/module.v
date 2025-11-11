
module adder (
    input [7:0] a,
    input [7:0] b,
    output [7:0] s,
    output overflow
);

wire [8:0] sum;
wire carry;

assign {carry, sum} = a + b;

assign overflow = (a[7] == b[7]) && (a[7] != s[7]);

assign s = sum[7:0];

endmodule
module xor_module (
    input [7:0] in,
    output [7:0] out
);

assign out = in ^ 8'b10101010;

endmodule
module top_module (
    input [7:0] a,
    input [7:0] b,
    output [7:0] s,
    output overflow,
    output [7:0] out
);

wire [7:0] adder_out;

adder adder_inst (.a(a), .b(b), .s(adder_out), .overflow(overflow));
xor_module xor_inst (.in(adder_out), .out(out));

assign s = adder_out;

endmodule