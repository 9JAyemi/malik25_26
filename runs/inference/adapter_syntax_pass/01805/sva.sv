module multiplier_sva (
    input logic [7:0] num1,
    input logic [7:0] num2,
    input logic [15:0] product
);

    // product must equal the 8x8 unsigned multiplication of num1 and num2.
    check_product_matches_multiplication: assert property (
        @($global_clock) product == (num1 * num2)
    );

    // A zero multiplicand must produce a zero product.
    check_zero_multiplicand: assert property (
        @($global_clock) (num1 == 8'h00) |-> (product == 16'h0000)
    );

    // A zero multiplier must produce a zero product.
    check_zero_multiplier: assert property (
        @($global_clock) (num2 == 8'h00) |-> (product == 16'h0000)
    );

    // Multiplying by one on num1 must pass num2 through to product.
    check_num1_one_passthrough: assert property (
        @($global_clock) (num1 == 8'h01) |-> (product == {8'h00, num2})
    );

    // Multiplying by one on num2 must pass num1 through to product.
    check_num2_one_passthrough: assert property (
        @($global_clock) (num2 == 8'h01) |-> (product == {8'h00, num1})
    );

    // Multiplying by eight on num1 must shift num2 three bits left.
    check_num1_eight_shift: assert property (
        @($global_clock) (num1 == 8'h08) |-> (product == ({num2, 1'b0} << 3))
    );

    // Multiplying by eight on num2 must shift num1 three bits left.
    check_num2_eight_shift: assert property (
        @($global_clock) (num2 == 8'h08) |-> (product == ({num1, 1'b0} << 3))
    );

    // Multiplying by 0x80 on num1 must produce zero because the result is 16 bits wide.
    check_num1_80_zero: assert property (
        @($global_clock) (num1 == 8'h80) |-> (product == 16'h0000)
    );

    // Multiplying by 0x80 on num2 must produce zero because the result is 16 bits wide.
    check_num2_80_zero: assert property (
        @($global_clock) (num2 == 8'h80) |-> (product == 16'h0000)
    );

endmodule