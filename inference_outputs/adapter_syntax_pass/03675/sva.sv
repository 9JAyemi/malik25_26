module ternary_add_sva #(parameter WIDTH = 8, parameter SIGN_EXT = 1'b0) (
    input logic clk,
    input logic [WIDTH-1:0] a,
    input logic [WIDTH-1:0] b,
    input logic [WIDTH-1:0] c,
    input logic [WIDTH+1:0] o
);

    // In non-sign-extended mode, o must equal the 3-bit sum of a, b, and c.
    check_non_sign_extended_sum: assert property (
        @(posedge clk) disable iff (1'b0)
        (!SIGN_EXT) |-> (o == {1'b0, a[WIDTH-1], a[WIDTH-2], a[WIDTH-3]} +
                            {1'b0, b[WIDTH-1], b[WIDTH-2], b[WIDTH-3]} +
                            {1'b0, c[WIDTH-1], c[WIDTH-2], c[WIDTH-3]})
    );

    // In sign-extended mode, o must equal the 3-bit sum of the sign-extended inputs.
    check_sign_extended_sum: assert property (
        @(posedge clk) disable iff (1'b0)
        SIGN_EXT |-> (o == {1'b0, a[WIDTH-1], a[WIDTH-2], a[WIDTH-3]} +
                           {1'b0, b[WIDTH-1], b[WIDTH-2], b[WIDTH-3]} +
                           {1'b0, c[WIDTH-1], c[WIDTH-2], c[WIDTH-3]})
    );

    // In non-sign-extended mode, the upper two output bits must be zero.
    check_non_sign_extended_upper_bits_zero: assert property (
        @(posedge clk) disable iff (1'b0)
        (!SIGN_EXT) |-> (o[WIDTH+1:WIDTH] == 2'b00)
    );

    // In sign-extended mode, the upper two output bits must be zero.
    check_sign_extended_upper_bits_zero: assert property (
        @(posedge clk) disable iff (1'b0)
        SIGN_EXT |-> (o[WIDTH+1:WIDTH] == 2'b00)
    );

    // In non-sign-extended mode, the least-significant output bit must match a[WIDTH-3].
    check_non_sign_extended_lsb_from_a: assert property (
        @(posedge clk) disable iff (1'b0)
        (!SIGN_EXT) |-> (o[0] == a[WIDTH-3])
    );

    // In sign-extended mode, the least-significant output bit must match a[WIDTH-3].
    check_sign_extended_lsb_from_a: assert property (
        @(posedge clk) disable iff (1'b0)
        SIGN_EXT |-> (o[0] == a[WIDTH-3])
    );

endmodule