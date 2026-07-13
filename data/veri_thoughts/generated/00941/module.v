
module top_module (
    input [7:0] d_in, // Input to the second module
    input [7:0] a, b, c, d, // Inputs to the first module
    output [7:0] max // Maximum value obtained from the sum
);

wire [7:0] sum_out;

module_1 m1(.a(a), .b(b), .c(c), .d(d), .out(sum_out));
module_2 m2(.in(sum_out), .out(max));

endmodule
module module_1 (
    input [7:0] a, b, c, d,
    output [7:0] out
);

assign out = a + b + c + d;

endmodule
module module_2 (
    input [7:0] in,
    output [7:0] out
);

assign out = in;

endmodule