
module adder (
    input [3:0] a,
    input [3:0] b,
    output [3:0] sum
);

    assign sum = a + b;

endmodule
module multiplier (
    input [3:0] a,
    input [3:0] b,
    output [7:0] product
);

    assign product = a * b;

endmodule
module final_module (
    input [3:0] sum,
    input [7:0] product,
    output [7:0] final_output
);

    assign final_output = (sum * 2) + (product / 2);

endmodule
module top_module (
    input clk,
    input reset,
    input [3:0] a,
    input [3:0] b,
    output [3:0] sum,
    output [7:0] product,
    output [7:0] final_output
);

    wire [3:0] sum_wire;
    wire [7:0] product_wire;

    adder adder_inst (
        .a(a),
        .b(b),
        .sum(sum_wire)
    );

    multiplier multiplier_inst (
        .a(a),
        .b(b),
        .product(product_wire)
    );

    final_module final_inst (
        .sum(sum_wire),
        .product(product_wire),
        .final_output(final_output)
    );

    assign sum = sum_wire;
    assign product = product_wire;

endmodule