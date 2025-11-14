module top_module(
    input [31:0] a,
    input [31:0] b,
    output [31:0] out
);

wire [31:0] adder_output;

adder_32bit adder_inst (
    .a(a),
    .b(b),
    .sum(adder_output)
);

byte_reverser reverser_inst (
    .input_data(adder_output),
    .output_data(out)
);

endmodule

module adder_32bit(
    input [31:0] a,
    input [31:0] b,
    output [31:0] sum
);

wire [7:0] adder_output_0, adder_output_1, adder_output_2, adder_output_3;

adder_8bit adder_0 (
    .a(a[7:0]),
    .b(b[7:0]),
    .sum(adder_output_0)
);

adder_8bit adder_1 (
    .a(a[15:8]),
    .b(b[15:8]),
    .sum(adder_output_1)
);

adder_8bit adder_2 (
    .a(a[23:16]),
    .b(b[23:16]),
    .sum(adder_output_2)
);

adder_8bit adder_3 (
    .a(a[31:24]),
    .b(b[31:24]),
    .sum(adder_output_3)
);

assign sum = {adder_output_3, adder_output_2, adder_output_1, adder_output_0};

endmodule

module adder_8bit(
    input [7:0] a,
    input [7:0] b,
    output [7:0] sum
);

assign sum = a + b;

endmodule

module byte_reverser(
    input [31:0] input_data,
    output [31:0] output_data
);

assign output_data = {input_data[7:0], input_data[15:8], input_data[23:16], input_data[31:24]};

endmodule