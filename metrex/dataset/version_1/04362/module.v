
module top_module (
    input [7:0] a,
    input [7:0] b,
    output [7:0] s,
    output overflow,
    output [7:0] final_output
);

wire [15:0] product;
wire [8:0] sum;
wire msb_in_a, msb_in_b, msb_out;
assign msb_in_a = a[7];
assign msb_in_b = b[7];

wire [8:0] product_1;
wire [8:0] product_2;
wire [8:0] product_3;
wire [8:0] product_4;
wire [8:0] product_5;
wire [8:0] product_6;
wire [8:0] product_7;
wire [8:0] product_8;

assign product_1 = a[7] * b[0];
assign product_2 = a[7] * b[1];
assign product_3 = a[7] * b[2];
assign product_4 = a[7] * b[3];
assign product_5 = a[7] * b[4];
assign product_6 = a[7] * b[5];
assign product_7 = a[7] * b[6];
assign product_8 = a[7] * b[7];

assign product = {product_8, product_7, product_6, product_5, product_4, product_3, product_2, product_1};

assign sum = product[7:0] + product[15:8];

assign s = sum[7:0];
assign msb_out = sum[8];

assign overflow = (msb_in_a == msb_in_b) && (msb_in_a != msb_out);

overflow_detector od (
    .overflow(overflow),
    .sum(sum),
    .final_output(final_output)
);

endmodule
module overflow_detector (
    input overflow,
    input [8:0] sum,
    output [7:0] final_output
);
    assign final_output = overflow ? sum[7:0] : sum[7:0];
endmodule