module ternary_add_sva (
    input logic clk,
    input logic [7:0] a,
    input logic [7:0] b,
    input logic [7:0] c,
    input logic [8:0] o
);

// No reset in RTL; sample on clk.

    // In non-sign-extend mode, o equals a+b+c truncated to 8 bits.
    check_nonsext_sum_trunc: assert property (
        @(posedge clk) (!SIGN_EXT) |-> (o == ((a + b + c) & 8'hFF))
    );

// In sign-extend mode, o equals 32-bit a+b+c with sign extension.
    check_sext_sum_signext: assert property (
        @(posedge clk) (SIGN_EXT) |-> (o == {1'b0, a[7], a, b[7], b, c[7], c} + 9'h000)
    );

// In non-sign-extend mode, o[7:0] equals a+b+c.
    check_nonsext_lower_byte: assert property (
        @(posedge clk) (!SIGN_EXT) |-> (o[7:0] == (a + b + c))
    );

// In non-sign-extend mode, o[8] is the carry-out of a+b+c.
    check_nonsext_carry_out: assert property (
        @(posedge clk) (!SIGN_EXT) |-> (o[8] == ((a + b + c) > 8'hFF))
    );

// In sign-extend mode, o[8] is the sign bit of the 32-bit sum.
    check_sext_sign_bit: assert property (
        @(posedge clk) (SIGN_EXT) |-> (o[8] == (({1'b0, a[7], a, b[7], b, c[7], c} + 9'h000) >> 8))
    );

// In sign-extend mode, o[7:1] equals the upper 7 bits of the 32-bit sum.
    check_sext_upper_bits: assert property (
        @(posedge clk) (SIGN_EXT) |-> (o[7:1] == (({1'b0, a[7], a, b[7], b, c[7], c} + 9'h000) >> 1))
    );

endmodule
