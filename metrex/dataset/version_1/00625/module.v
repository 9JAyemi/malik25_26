module top_module (
    input clk,
    input reset,      // Synchronous active-high reset
    input [7:0] d1,   // 8-bit input for the first register
    input [7:0] d2,   // 8-bit input for the second register
    output [7:0] q    // 8-bit output from the multiplication module
);

    reg [7:0] reg1, reg2;   // Two 8-bit registers
    wire [7:0] add_result;  // Output from the adder module
    wire [7:0] mul_result;  // Output from the multiplication module

    // Instantiate the adder module
    adder_module adder(
        .a(reg1),
        .b(reg2),
        .sum(add_result)
    );

    // Instantiate the multiplication module
    multiplication_module multiplier(
        .a(add_result),
        .b(5),
        .product(mul_result)
    );

    // Register logic with synchronous reset
    always @(posedge clk) begin
        if (reset) begin
            reg1 <= 0;
            reg2 <= 0;
        end else begin
            reg1 <= d1;
            reg2 <= d2;
        end
    end

    assign q = mul_result;  // Assign output to the multiplication result

endmodule

// Adder module
module adder_module (
    input [7:0] a,
    input [7:0] b,
    output reg [7:0] sum
);

    always @(a, b) begin
        sum <= a + b;
    end

endmodule

// Multiplication module
module multiplication_module (
    input [7:0] a,
    input [7:0] b,
    output reg [7:0] product
);

    always @(a, b) begin
        product <= a * b;
    end

endmodule