
module top_module (
    input clk,
    input reset,
    input [7:0] a1,
    input [7:0] b1,
    input [7:0] a2,
    input [7:0] b2,
    output EN,
    output [2:0] Y
);

    // Instantiate unsigned multiplier modules
    wire [15:0] product1;
    wire [15:0] product2;
    unsigned_multiplier unsigned_multiplier_1(a1, b1, clk, reset, product1);
    unsigned_multiplier unsigned_multiplier_2(a2, b2, clk, reset, product2);

    // Instantiate priority encoder module
    priority_encoder priority_encoder(product1, product2, EN, Y);

endmodule
module unsigned_multiplier (
    input [7:0] a,
    input [7:0] b,
    input clk,
    input reset,
    output [15:0] product
);

    reg [15:0] product_reg;

    always @(posedge clk) begin
        if (reset) begin
            product_reg <= 0;
        end else begin
            product_reg <= a * b;
        end
    end

    assign product = product_reg;

endmodule
module priority_encoder (
    input [15:0] inputs1,
    input [15:0] inputs2,
    output reg EN,
    output reg [2:0] Y
);

    always @(*) begin
        if (inputs1 == 16'h0000 && inputs2 == 16'h0000) begin
            EN <= 0;
            Y <= 3'b000;
        end else if (inputs1 > inputs2) begin
            EN <= 1;
            Y <= inputs1[12:10];
        end else begin
            EN <= 1;
            Y <= inputs2[12:10];
        end
    end

endmodule