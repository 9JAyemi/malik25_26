module multiplier_4bit_sva (
    input logic [3:0] A,
    input logic [3:0] B,
    input logic [7:0] P
);

    // Combinational DUT sampled on the formal global clock.

    // P always matches the product of A and B.
    check_product_value: assert property (
        @($global_clock) P == (A * B)
    );

    // If either operand is zero, the product is zero.
    check_zero_operand: assert property (
        @($global_clock) ((A == 4'd0) || (B == 4'd0)) |-> (P == 8'd0)
    );

    // If A is one, P equals B with zero extension.
    check_a_is_one: assert property (
        @($global_clock) (A == 4'd1) |-> (P == {4'b0000, B})
    );

    // If B is one, P equals A with zero extension.
    check_b_is_one: assert property (
        @($global_clock) (B == 4'd1) |-> (P == {4'b0000, A})
    );

    // The maximum 4-bit operands produce 225.
    check_max_operands: assert property (
        @($global_clock) ((A == 4'hF) && (B == 4'hF)) |-> (P == 8'd225)
    );

    // The product never exceeds the maximum 4x4 unsigned result.
    check_product_range: assert property (
        @($global_clock) P <= 8'd225
    );

endmodule