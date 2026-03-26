
module mul8 (
    input [7:0] a,
    input [7:0] b,
    output reg [15:0] product
);

always @(*) begin
    product = a * b;
end

endmodule
module sum_module (
    input signed [15:0] a,
    input signed [15:0] b,
    output signed [15:0] sum
);

assign sum = a + b;

endmodule
module top_module (
    input signed [15:0] a,
    input signed [15:0] b,
    output signed [31:0] product_sum
);

wire [15:0] a_unsigned = {1'b0, a[15:0]};
wire [15:0] b_unsigned = {1'b0, b[15:0]};

wire [15:0] product_low;
wire [15:0] product_high;

mul8 mul8_low(a_unsigned[7:0], b_unsigned[7:0], product_low);
mul8 mul8_high(a_unsigned[15:8], b_unsigned[15:8], product_high);

assign product_sum[31:16] = product_high + product_low;

assign product_sum[15:0] = product_low;

endmodule