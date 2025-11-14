module mul16(
    input [15:0] a,
    input [15:0] b,
    output reg [31:0] result
);

always @(*) begin
    result = a * b;
end

endmodule

module top_module(
    input [31:0] a,
    input [31:0] b,
    input enable,
    output [31:0] result
);

wire [15:0] a_low = a[15:0];
wire [15:0] a_high = a[31:16];
wire [15:0] b_low = b[15:0];
wire [15:0] b_high = b[31:16];

wire [31:0] mul_low;
wire [31:0] mul_high;

mul16 mul1(
    .a(a_low),
    .b(b_low),
    .result(mul_low)
);

mul16 mul2(
    .a(a_high),
    .b(b_high),
    .result(mul_high)
);

assign result = enable ? {mul_high, mul_low} : 0;

endmodule