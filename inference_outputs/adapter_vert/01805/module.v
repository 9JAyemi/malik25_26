module multiplier(
    input wire [7:0] num1,
    input wire [7:0] num2,
    output wire [15:0] product
);

    assign product = num1 * num2;

endmodule

module top_module( 
    input wire [7:0] num1,
    input wire [7:0] num2,
    output wire [15:0] product
);

    multiplier mult(.num1(num1), .num2(num2), .product(product));

endmodule