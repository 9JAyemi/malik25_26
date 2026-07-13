
module binary_multiplier (
    input [3:0] a,
    input [3:0] b,
    output [7:0] product
);

    integer i; // Declare i as an integer for loop indexing

    reg [7:0] product; // Declare product as a reg

    always @ * begin
        product = 8'b0; // Initialize product to 0
        for (i = 0; i < 4; i = i + 1) begin
            if (b[i] == 1) begin
                product = product + (a << i);
            end
        end
    end

endmodule
module gray_code (
    input [3:0] binary_input,
    output [3:0] gray_output
);

    reg [3:0] gray_output; // Declare gray_output as a reg

    always @ * begin
        gray_output = binary_input ^ (binary_input >> 1);
    end

endmodule
module top_module (
    input clk,
    input reset,      // Synchronous active-high reset
    input [3:0] a,    // First 4-bit binary input
    input [3:0] b,    // Second 4-bit binary input
    output reg [3:0] gray_product // Final product in Gray code
);

    wire [7:0] binary_product;
    reg [7:0] binary_product_reg; // Declare binary_product_reg as a reg
    wire [3:0] binary_a;
    wire [3:0] binary_b;
    wire [3:0] gray_a;
    wire [3:0] gray_b;

    binary_multiplier binary_mult(.a(a), .b(b), .product(binary_product));
    gray_code gray_a_code(.binary_input(a), .gray_output(gray_a));
    gray_code gray_b_code(.binary_input(b), .gray_output(gray_b));

    always @(posedge clk) begin
        if (reset) begin
            binary_product_reg <= 8'b0;
            gray_product <= 4'b0;
        end else begin
            binary_product_reg <= binary_product;
            gray_product <= gray_a ^ gray_b; // Calculate gray product
        end
    end

endmodule