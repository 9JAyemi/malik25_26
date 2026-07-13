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

    // A zero operand must produce a zero result.
    check_zero_operand_forces_zero_result: assert property (
        @(posedge clk) ((A == 16'h0000) || (B == 16'h0000)) |-> (Z == 32'h00000000)
    );

    // A value of one on A must pass B through to Z.
    check_a_one_passthrough: assert property (
        @(posedge clk) (A == 16'h0001) |-> (Z == {16'h0000, B})
    );

    // A value of one on B must pass A through to Z.
    check_b_one_passthrough: assert property (
        @(posedge clk) (B == 16'h0001) |-> (Z == {16'h0000, A})
    );

    // A value of 16'hFFFF on A must produce a 32-bit all-ones result.
    check_a_max_value: assert property (
        @(posedge clk) (A == 16'hFFFF) |-> (Z == 32'hFFFFFFFF)
    );

    // A value of 16'hFFFF on B must produce a 32-bit all-ones result.
    check_b_max_value: assert property (
        @(posedge clk) (B == 16'hFFFF) |-> (Z == 32'hFFFFFFFF)
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

    // A zero operand must produce a zero result.
    check_zero_operand_forces_zero_result: assert property (
        @(posedge clk) ((A == 20'h00000) || (B == 18'h00000)) |-> (Z == 38'h000000000)
    );

    // A value of one on A must pass B through to Z.
    check_a_one_passthrough: assert property (
        @(posedge clk) (A == 20'h00001) |-> (Z == {18'h00000, B})
    );

    // A value of one on B must pass A through to Z.
    check_b_one_passthrough: assert property (
        @(posedge clk) (B == 18'h00001) |-> (Z == {20'h00000, A})
    );

    // A value of 20'hFFFFF on A must produce a 38-bit all-ones result.
    check_a_max_value: assert property (
        @(posedge clk) (A == 20'hFFFFF) |-> (Z == 38'hFFFFFFFFF)
    );

    // A value of 18'hFFFFF on B must produce a 38-bit all-ones result.
    check_b_max_value: assert property (
        @(posedge clk) (B == 18'hFFFFF) |-> (Z == 38'hFFFFFFFFF)
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

    // A zero operand must produce a zero result.
    check_zero_operand_forces_zero_result: assert property (
        @(posedge clk) ((A == 8'h00) || (B == 8'h00)) |-> (Z == 16'h0000)
    );

    // A value of one on A must pass B through to Z.
    check_a_one_passthrough: assert property (
        @(posedge clk) (A == 8'h01) |-> (Z == {8'h00, B})
    );

    // A value of one on B must pass A through to Z.
    check_b_one_passthrough: assert property (
        @(posedge clk) (B == 8'h01) |-> (Z == {8'h00, A})
    );

    // A value of 8'hFF on A must produce a 16-bit all-ones result.
    check_a_max_value: assert property (
        @(posedge clk) (A == 8'hFF) |-> (Z == 16'hFFFF)
    );

    // A value of 8'hFF on B must produce a 16-bit all-ones result.
    check_b_max_value: assert property (
        @(posedge clk) (B == 8'hFF) |-> (Z == 16'hFFFF)
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

    // A zero operand must produce a zero result.
    check_zero_operand_forces_zero_result: assert property (
        @(posedge clk) ((A == 10'h000) || (B == 9'h000)) |-> (Z == 19'h00000)
    );

    // A value of one on A must pass B through to Z.
    check_a_one_passthrough: assert property (
        @(posedge clk) (A == 10'h001) |-> (Z == {9'h000, B})
    );

    // A value of one on B must pass A through to Z.
    check_b_one_passthrough: assert property (
        @(posedge clk) (B == 9'h001) |-> (Z == {10'h000, A})
    );

    // A value of 10'h3FF on A must produce a 19-bit all-ones result.
    check_a_max_value: assert property (
        @(posedge clk) (A == 10'h3FF) |-> (Z == 19'h1FFFF)
    );

    // A value of 9'h1FF on B must produce a 19-bit all-ones result.
    check_b_max_value: assert property (
        @(posedge clk) (B == 9'h1FF) |-> (Z == 19'h1FFFF)
    );

endmodule