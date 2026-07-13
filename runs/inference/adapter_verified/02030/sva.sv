module mult_16x16_sva (
    input logic        clk,
    input logic [15:0] A,
    input logic [15:0] B,
    input logic [31:0] Z
);

// Z must equal the 32-bit product of A and B.
    check_product_16x16: assert property (
        @(posedge clk) Z == (A * B)
    );

// Zero on A must produce zero on Z.
    check_zero_a: assert property (
        @(posedge clk) (A == 16'h0000) |-> (Z == 32'h0000_0000)
    );

// Zero on B must produce zero on Z.
    check_zero_b: assert property (
        @(posedge clk) (B == 16'h0000) |-> (Z == 32'h0000_0000)
    );

// Maximum 16-bit values must produce the maximum 32-bit product.
    check_max_product: assert property (
        @(posedge clk) ((A == 16'hFFFF) && (B == 16'hFFFF)) |-> (Z == 32'hFFFF_FFFF)
    );

endmodule

module mult_20x18_sva (
    input logic        clk,
    input logic [19:0] A,
    input logic [17:0] B,
    input logic [37:0] Z
);

// Z must equal the 38-bit product of A and B.
    check_product_20x18: assert property (
        @(posedge clk) Z == (A * B)
    );

// Zero on A must produce zero on Z.
    check_zero_a: assert property (
        @(posedge clk) (A == 20'h00000) |-> (Z == 38'h0000_0000_0000)
    );

// Zero on B must produce zero on Z.
    check_zero_b: assert property (
        @(posedge clk) (B == 18'h00000) |-> (Z == 38'h0000_0000_0000)
    );

// Maximum 20-bit A and 18-bit B must produce the maximum 38-bit product.
    check_max_product: assert property (
        @(posedge clk) ((A == 20'hFFFFF) && (B == 18'hFFFFF)) |-> (Z == 38'hFFFF_FFFF_FFFF)
    );

endmodule

module mult_8x8_sva (
    input logic        clk,
    input logic [ 7:0] A,
    input logic [ 7:0] B,
    input logic [15:0] Z
);

// Z must equal the 16-bit product of A and B.
    check_product_8x8: assert property (
        @(posedge clk) Z == (A * B)
    );

// Zero on A must produce zero on Z.
    check_zero_a: assert property (
        @(posedge clk) (A == 8'h00) |-> (Z == 16'h0000)
    );

// Zero on B must produce zero on Z.
    check_zero_b: assert property (
        @(posedge clk) (B == 8'h00) |-> (Z == 16'h0000)
    );

// Maximum 8-bit values must produce the maximum 16-bit product.
    check_max_product: assert property (
        @(posedge clk) ((A == 8'hFF) && (B == 8'hFF)) |-> (Z == 16'hFFFF)
    );

endmodule

module mult_10x9_sva (
    input logic        clk,
    input logic [ 9:0] A,
    input logic [ 8:0] B,
    input logic [18:0] Z
);

// Z must equal the 19-bit product of A and B.
    check_product_10x9: assert property (
        @(posedge clk) Z == (A * B)
    );

// Zero on A must produce zero on Z.
    check_zero_a: assert property (
        @(posedge clk) (A == 10'h000) |-> (Z == 19'h0000_0000)
    );

// Zero on B must produce zero on Z.
    check_zero_b: assert property (
        @(posedge clk) (B == 9'h000) |-> (Z == 19'h0000_0000)
    );

// Maximum 10-bit A and 9-bit B must produce the maximum 19-bit product.
    check_max_product: assert property (
        @(posedge clk) ((A == 10'h3FF) && (B == 9'h1FF)) |-> (Z == 19'hFFFF_F)
    );

endmodule
