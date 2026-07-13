module modulo_sva (
    input logic        clk,
    input logic [31:0] a,
    input logic [31:0] b,
    input logic [31:0] r
);

    // A zero divisor forces the result to zero.
    check_divide_by_zero_returns_zero: assert property (
        @(posedge clk) (b == 32'd0) |-> (r == 32'd0)
    );

    // A nonzero divisor produces the Verilog modulo result.
    check_nonzero_divisor_matches_modulo: assert property (
        @(posedge clk) (b != 32'd0) |-> (r == (a % b))
    );

    // For a nonzero divisor, the remainder is smaller than the divisor.
    check_remainder_less_than_divisor: assert property (
        @(posedge clk) (b != 32'd0) |-> (r < b)
    );

    // A zero dividend always produces a zero remainder.
    check_zero_dividend_returns_zero: assert property (
        @(posedge clk) (a == 32'd0) |-> (r == 32'd0)
    );

    // If the dividend is smaller than a nonzero divisor, the remainder equals the dividend.
    check_small_dividend_passes_through: assert property (
        @(posedge clk) ((b != 32'd0) && (a < b)) |-> (r == a)
    );

    // Dividing by one always produces a zero remainder.
    check_divisor_one_gives_zero_remainder: assert property (
        @(posedge clk) (b == 32'd1) |-> (r == 32'd0)
    );

    // For a nonzero divisor, quotient and remainder reconstruct the dividend.
    check_dividend_reconstruction: assert property (
        @(posedge clk) (b != 32'd0) |-> (a == ((a / b) * b + r))
    );

endmodule