module mult_16x16_sva (
    input logic        clk,
    input logic [15:0] A,
    input logic [15:0] B,
    input logic [31:0] Z
);

    // Z must equal the 32-bit product of A and B.
    check_product_matches_inputs: assert property (
        @(posedge clk) Z == (A * B)
    );

    // A zero operand must produce a zero product.
    check_zero_operand_zero_product: assert property (
        @(posedge clk) ((A == 16'h0000) || (B == 16'h0000)) |-> (Z == 32'h00000000)
    );

    // Multiplying by one on A must pass B through unchanged.
    check_one_operand_passthrough_a: assert property (
        @(posedge clk) (A == 16'h0001) |-> (Z == {16'h0000, B})
    );

    // Multiplying by one on B must pass A through unchanged.
    check_one_operand_passthrough_b: assert property (
        @(posedge clk) (B == 16'h0001) |-> (Z == {16'h0000, A})
    );

    // The least-significant byte of Z must equal the low-byte product.
    check_low_byte_matches_low_byte_product: assert property (
        @(posedge clk) Z[7:0] == (A[7:0] * B[7:0])
    );

    // The upper 16 bits of Z must be zero when either operand is zero.
    check_upper_half_zero_when_operand_zero: assert property (
        @(posedge clk) ((A == 16'h0000) || (B == 16'h0000)) |-> (Z[31:16] == 16'h0000)
    );

endmodule

module mult_20x18_sva (
    input logic        clk,
    input logic [19:0] A,
    input logic [17:0] B,
    input logic [37:0] Z
);

    // Z must equal the 38-bit product of A and B.
    check_product_matches_inputs: assert property (
        @(posedge clk) Z == (A * B)
    );

    // A zero operand must produce a zero product.
    check_zero_operand_zero_product: assert property (
        @(posedge clk) ((A == 20'h00000) || (B == 18'h00000)) |-> (Z == 38'h000000000)
    );

    // Multiplying by one on A must pass B through unchanged.
    check_one_operand_passthrough_a: assert property (
        @(posedge clk) (A == 20'h00001) |-> (Z == {18'h00000, B})
    );

    // Multiplying by one on B must pass A through unchanged.
    check_one_operand_passthrough_b: assert property (
        @(posedge clk) (B == 18'h00001) |-> (Z == {20'h00000, A})
    );

    // The least-significant byte of Z must equal the low-byte product.
    check_low_byte_matches_low_byte_product: assert property (
        @(posedge clk) Z[7:0] == (A[7:0] * B[7:0])
    );

    // The upper 20 bits of Z must be zero when either operand is zero.
    check_upper_half_zero_when_operand_zero: assert property (
        @(posedge clk) ((A == 20'h00000) || (B == 18'h00000)) |-> (Z[37:18] == 20'h00000)
    );

endmodule

module mult_8x8_sva (
    input logic        clk,
    input logic [ 7:0] A,
    input logic [ 7:0] B,
    input logic [15:0] Z
);

    // Z must equal the 16-bit product of A and B.
    check_product_matches_inputs: assert property (
        @(posedge clk) Z == (A * B)
    );

    // A zero operand must produce a zero product.
    check_zero_operand_zero_product: assert property (
        @(posedge clk) ((A == 8'h00) || (B == 8'h00)) |-> (Z == 16'h0000)
    );

    // Multiplying by one on A must pass B through unchanged.
    check_one_operand_passthrough_a: assert property (
        @(posedge clk) (A == 8'h01) |-> (Z == {8'h00, B})
    );

    // Multiplying by one on B must pass A through unchanged.
    check_one_operand_passthrough_b: assert property (
        @(posedge clk) (B == 8'h01) |-> (Z == {8'h00, A})
    );

    // The least-significant byte of Z must equal the low-byte product.
    check_low_byte_matches_low_byte_product: assert property (
        @(posedge clk) Z[7:0] == (A[7:0] * B[7:0])
    );

    // The upper 8 bits of Z must be zero when either operand is zero.
    check_upper_half_zero_when_operand_zero: assert property (
        @(posedge clk) ((A == 8'h00) || (B == 8'h00)) |-> (Z[15:8] == 8'h00)
    );

endmodule

module mult_10x9_sva (
    input logic        clk,
    input logic [ 9:0] A,
    input logic [ 8:0] B,
    input logic [18:0] Z
);

    // Z must equal the 19-bit product of A and B.
    check_product_matches_inputs: assert property (
        @(posedge clk) Z == (A * B)
    );

    // A zero operand must produce a zero product.
    check_zero_operand_zero_product: assert property (
        @(posedge clk) ((A == 10'h000) || (B == 9'h000)) |-> (Z == 19'h00000)
    );

    // Multiplying by one on A must pass B through unchanged.
    check_one_operand_passthrough_a: assert property (
        @(posedge clk) (A == 10'h001) |-> (Z == {9'h000, B})
    );

    // Multiplying by one on B must pass A through unchanged.
    check_one_operand_passthrough_b: assert property (
        @(posedge clk) (B == 9'h001) |-> (Z == {10'h000, A})
    );

    // The least-significant byte of Z must equal the low-byte product.
    check_low_byte_matches_low_byte_product: assert property (
        @(posedge clk) Z[7:0] == (A[7:0] * B[7:0])
    );

    // The upper 10 bits of Z must be zero when either operand is zero.
    check_upper_half_zero_when_operand_zero: assert property (
        @(posedge clk) ((A == 10'h000) || (B == 9'h000)) |-> (Z[18:9] == 10'h000)
    );

endmodule