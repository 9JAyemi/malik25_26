module mult_16x16_sva (
    input logic        clk,
    input logic [15:0] A,
    input logic [15:0] B,
    input logic [31:0] Z
);

    // Z must match the unsigned 16x16 product.
    check_mult_16x16_product_match: assert property (
        @(posedge clk) disable iff (1'b0) Z == (A * B)
    );

    // A zero operand must produce a zero result.
    check_mult_16x16_zero_operand_zero_result: assert property (
        @(posedge clk) disable iff (1'b0) ((A == 16'd0) || (B == 16'd0)) |-> (Z == 32'd0)
    );

endmodule

module mult_20x18_sva (
    input logic        clk,
    input logic [19:0] A,
    input logic [17:0] B,
    input logic [37:0] Z
);

    // Z must match the unsigned 20x18 product.
    check_mult_20x18_product_match: assert property (
        @(posedge clk) disable iff (1'b0) Z == (A * B)
    );

    // Multiplying by one on B must pass A through unchanged.
    check_mult_20x18_unit_multiplicand: assert property (
        @(posedge clk) disable iff (1'b0) (B == 18'd1) |-> (Z == {{18{1'b0}}, A})
    );

endmodule

module mult_8x8_sva (
    input logic       clk,
    input logic [7:0] A,
    input logic [7:0] B,
    input logic [15:0] Z
);

    // Z must match the unsigned 8x8 product.
    check_mult_8x8_product_match: assert property (
        @(posedge clk) disable iff (1'b0) Z == (A * B)
    );

    // Multiplying by one on A must pass B through unchanged.
    check_mult_8x8_unit_multiplicand: assert property (
        @(posedge clk) disable iff (1'b0) (A == 8'd1) |-> (Z == {{8{1'b0}}, B})
    );

endmodule

module mult_10x9_sva (
    input logic        clk,
    input logic [ 9:0] A,
    input logic [ 8:0] B,
    input logic [18:0] Z
);

    // Z must match the unsigned 10x9 product.
    check_mult_10x9_product_match: assert property (
        @(posedge clk) disable iff (1'b0) Z == (A * B)
    );

    // A zero operand must produce a zero result.
    check_mult_10x9_zero_operand_zero_result: assert property (
        @(posedge clk) disable iff (1'b0) ((A == 10'd0) || (B == 9'd0)) |-> (Z == 19'd0)
    );

endmodule

module mult_8x8_s_signed_sva (
    input logic              clk,
    input logic signed [7:0] A,
    input logic signed [7:0] B,
    input logic signed [15:0] Z
);

    // Z must match the signed 8x8 product.
    check_mult_8x8_s_product_match: assert property (
        @(posedge clk) disable iff (1'b0) Z == (A * B)
    );

    // Multiplying by one on B must preserve A with sign extension.
    check_mult_8x8_s_unit_multiplicand: assert property (
        @(posedge clk) disable iff (1'b0) (B == 8'sd1) |-> (Z == {{8{A[7]}}, A})
    );

endmodule