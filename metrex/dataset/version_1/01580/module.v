
module adder(
    input [7:0] a,
    input [7:0] b,
    output [7:0] sum
);

assign sum = a + b;

endmodule
module average(
    input [7:0] a,
    input [7:0] b,
    input [7:0] c,
    output [7:0] result
);

wire [7:0] sum;
wire [7:0] divisor = 3;

adder adder1(.a(a), .b(b), .sum(sum));
adder adder2(.a(sum), .b(c), .sum(result));

endmodule
module top_module(
    input [7:0] a,
    input [7:0] b,
    input [7:0] c,
    output [7:0] result
);

average avg(.a(a), .b(b), .c(c), .result(result));

endmodule