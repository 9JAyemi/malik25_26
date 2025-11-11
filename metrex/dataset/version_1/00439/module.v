
module top_module(
    input wire [7:0] in1,
    input wire [7:0] in2,
    output wire [7:0] out
);

    // Splitting inputs into 4-bit values
    wire [3:0] in1_hi, in1_lo;
    wire [3:0] in2_hi, in2_lo;
    assign in1_hi = in1[7:4];
    assign in1_lo = in1[3:0];
    assign in2_hi = in2[7:4];
    assign in2_lo = in2[3:0];

    // Adding corresponding 4-bit values
    wire [3:0] sum1, sum2;
    adder_4bit add1(.in1(in1_hi), .in2(in2_hi), .sum(sum1));
    adder_4bit add2(.in1(in1_lo), .in2(in2_lo), .sum(sum2));

    // Adding the total sum
    wire [7:0] out_sum;
    adder_8bit add3(.in1({4'b0, sum1}), .in2({4'b0, sum2}), .sum(out_sum));

    // Dividing by 4 to get the average
    assign out = {out_sum[7], out_sum[7:0] >> 2};

endmodule
module split_1_4bit(
    input wire [7:0] in,
    output wire [3:0] hi,
    output wire [3:0] lo
);

    assign hi = in[7:4];
    assign lo = in[3:0];

endmodule
module adder_4bit(
    input wire [3:0] in1,
    input wire [3:0] in2,
    output wire [3:0] sum
);

    assign sum = in1 + in2;

endmodule
module adder_8bit(
    input wire [7:0] in1,
    input wire [7:0] in2,
    output wire [7:0] sum
);

    assign sum = in1 + in2;

endmodule