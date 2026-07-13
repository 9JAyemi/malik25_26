module top_module ( 
    input clk, // Clock signal
    input reset, // Active high synchronous reset
    input [7:0] a, // 8-bit input a 
    input [7:0] b, // 8-bit input b
    input [7:0] c, // 8-bit input c
    output reg [15:0] sum // 16-bit output sum
);

    reg [15:0] product; // 16-bit output of multiplier module
    wire [15:0] add_input; // 16-bit input to adder module

    multiplier mult_module (
        .a(a),
        .b(b),
        .product(product)
    );

    adder add_module (
        .a(product),
        .b(c),
        .sum(add_input)
    );

    always @(posedge clk) begin
        if (reset) begin
            sum <= 16'b0;
        end else begin
            sum <= add_input;
        end
    end

endmodule

module multiplier (
    input [7:0] a,
    input [7:0] b,
    output reg [15:0] product
);

    always @(*) begin
        product = a * b;
    end

endmodule

module adder (
    input [15:0] a,
    input [7:0] b,
    output reg [15:0] sum
);

    always @(*) begin
        sum = a + {8'b0, b};
    end

endmodule