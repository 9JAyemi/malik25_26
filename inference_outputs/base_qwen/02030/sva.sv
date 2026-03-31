```systemverilog
module mult_assertions (
    input wire [15:0] A_16x16,
    input wire [15:0] B_16x16,
    output wire [31:0] Z_16x16,
    input wire [19:0] A_20x18,
    input wire [17:0] B_20x18,
    output wire [37:0] Z_20x18,
    input wire [ 7:0] A_8x8,
    input wire [ 7:0] B_8x8,
    output wire [15:0] Z_8x8,
    input wire [ 9:0] A_10x9,
    input wire [ 8:0] B_10x9,
    output wire [18:0] Z_10x9
);

    // 16x16 multiplier
    // Z_16x16 should be the product of A_16x16 and B_16x16
    mult_16x16_property: assert property (
        @(posedge clk) disable iff (!rst_n) Z_16x16 == A_16x16 * B_16x16
    );

    // 20x18 multiplier
    // Z_20x18 should be the product of A_20x18 and B_20x18
    mult_20x18_property: assert property (
        @(posedge clk) disable iff (!rst_n) Z_20x18 == A_20x18 * B_20x18
    );

    // 8x8 multiplier
    // Z_8x8 should be the product of A_8x8 and B_8x8
    mult_8x8_property: assert property (
        @(posedge clk) disable iff (!rst_n) Z_8x8 == A_8x8 * B_8x8
    );

    // 10x9 multiplier
    // Z_10x9 should be the product of A_10x9 and B_10x9
    mult_10x9_property: assert property (
        @(posedge clk) disable iff (!rst_n) Z_10x9 == A_10x9 * B_10x9
    );

endmodule
```