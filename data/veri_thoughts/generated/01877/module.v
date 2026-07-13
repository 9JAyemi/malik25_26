
module mul16(
    input [15:0] a,
    input [15:0] b,
    output reg [31:0] result
);

always @(*) begin
    result = a * b;
end

endmodule

module pipelined_multiplier(
    input [31:0] a,
    input [31:0] b,
    input enable,
    output reg [31:0] result
);

wire [15:0] a_lsb = a[15:0];
wire [15:0] a_msb = a[31:16];
wire [15:0] b_lsb = b[15:0];
wire [15:0] b_msb = b[31:16];

wire [31:0] mul16_1_result;
wire [31:0] mul16_2_result;

mul16 mul16_1(.a(a_lsb), .b(b_lsb), .result(mul16_1_result));
mul16 mul16_2(.a(a_msb), .b(b_msb), .result(mul16_2_result));

always @(posedge enable) begin
    result <= mul16_1_result + (mul16_2_result << 16);
end

endmodule
