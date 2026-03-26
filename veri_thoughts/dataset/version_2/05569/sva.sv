module unsigned_multiplier_sva (
    input logic        clk,
    input logic [15:0] a,
    input logic [15:0] b,
    input logic [31:0] result
);

    // Result always matches the unsigned product of the inputs.
    check_product_exact: assert property (
        @(posedge clk) result == (a * b)
    );

    // A zero on either input forces a zero result.
    check_zero_multiplicand: assert property (
        @(posedge clk) ((a == 16'd0) || (b == 16'd0)) |-> (result == 32'd0)
    );

    // Multiplying by one on a passes b through.
    check_a_is_one: assert property (
        @(posedge clk) (a == 16'd1) |-> (result == {16'd0, b})
    );

    // Multiplying by one on b passes a through.
    check_b_is_one: assert property (
        @(posedge clk) (b == 16'd1) |-> (result == {16'd0, a})
    );

    // The product LSB equals the AND of the input LSBs.
    check_product_lsb: assert property (
        @(posedge clk) result[0] == (a[0] & b[0])
    );

    // All-ones operands produce the maximum 16x16 unsigned product.
    check_max_operands: assert property (
        @(posedge clk) ((a == 16'hffff) && (b == 16'hffff)) |-> (result == 32'hfffe0001)
    );

endmodule