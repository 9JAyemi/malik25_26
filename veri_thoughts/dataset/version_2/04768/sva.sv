module Modulo_sva (
    input logic [31:0] a,
    input logic [31:0] b,
    input logic [31:0] result
);

    // No RTL clock or reset; sample this combinational logic on the formal global clock.

    // Result matches the modulo operation when the divisor is nonzero.
    check_result_matches_modulo: assert property (
        @($global_clock) (b != 32'd0) |-> (result == (a % b))
    );

    // For a nonzero divisor, the remainder is always smaller than the divisor.
    check_remainder_less_than_divisor: assert property (
        @($global_clock) (b != 32'd0) |-> (result < b)
    );

    // If the dividend is smaller than a nonzero divisor, the remainder equals the dividend.
    check_small_dividend_passthrough: assert property (
        @($global_clock) ((b != 32'd0) && (a < b)) |-> (result == a)
    );

    // Modulo by one always produces zero.
    check_modulo_by_one_zero: assert property (
        @($global_clock) (b == 32'd1) |-> (result == 32'd0)
    );

    // Equal nonzero operands produce a zero remainder.
    check_equal_operands_zero_result: assert property (
        @($global_clock) ((b != 32'd0) && (a == b)) |-> (result == 32'd0)
    );

    // A zero dividend with a nonzero divisor produces zero.
    check_zero_dividend_zero_result: assert property (
        @($global_clock) ((a == 32'd0) && (b != 32'd0)) |-> (result == 32'd0)
    );

endmodule