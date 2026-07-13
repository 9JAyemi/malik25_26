module ternary_add_sva #(
    parameter WIDTH = 8,
    parameter SIGN_EXT = 1'b0
) (
    input logic clk,
    input logic [WIDTH-1:0] a,
    input logic [WIDTH-1:0] b,
    input logic [WIDTH-1:0] c,
    input logic [WIDTH+1:0] o
);

    // In non-sign-extend mode, o matches the 3-input addition.
    check_non_sign_extend_add: assert property (
        @(posedge clk) disable iff (1'b0)
        (!SIGN_EXT) |-> (o == (a + b + c))
    );

    // In sign-extend mode, o matches the 3-input addition with sign extension.
    check_sign_extend_add: assert property (
        @(posedge clk) disable iff (1'b0)
        SIGN_EXT |-> (o == ({a[WIDTH-1], a[WIDTH-1], a} +
                             {b[WIDTH-1], b[WIDTH-1], b} +
                             {c[WIDTH-1], c[WIDTH-1], c}))
    );

    // In non-sign-extend mode, the low WIDTH bits match the 3-input sum.
    check_non_sign_extend_low_bits: assert property (
        @(posedge clk) disable iff (1'b0)
        (!SIGN_EXT) |-> (o[WIDTH-1:0] == (a + b + c))
    );

    // In sign-extend mode, the low WIDTH bits match the 3-input sum with sign extension.
    check_sign_extend_low_bits: assert property (
        @(posedge clk) disable iff (1'b0)
        SIGN_EXT |-> (o[WIDTH-1:0] == ({a[WIDTH-1], a[WIDTH-1], a} +
                                        {b[WIDTH-1], b[WIDTH-1], b} +
                                        {c[WIDTH-1], c[WIDTH-1], c}))
    );

    // In non-sign-extend mode, the carry-out is zero.
    check_non_sign_extend_carry_zero: assert property (
        @(posedge clk) disable iff (1'b0)
        (!SIGN_EXT) |-> (o[WIDTH+1] == 1'b0)
    );

    // In sign-extend mode, the carry-out is the sign bit of the 3-input sum.
    check_sign_extend_carry_sign: assert property (
        @(posedge clk) disable iff (1'b0)
        SIGN_EXT |-> (o[WIDTH+1] == (({a[WIDTH-1], a[WIDTH-1], a} +
                                      {b[WIDTH-1], b[WIDTH-1], b} +
                                      {c[WIDTH-1], c[WIDTH-1], c})[WIDTH-1]))
    );

    // If all inputs are zero, the output is zero.
    check_zero_inputs_zero_output: assert property (
        @(posedge clk) disable iff (1'b0)
        ((a == '0) && (b == '0) && (c == '0)) |-> (o == '0)
    );

    // If a is zero, the output reduces to b + c.
    check_a_zero_reduces_to_b_plus_c: assert property (
        @(posedge clk) disable iff (1'b0)
        (a == '0) |-> (o == (b + c))
    );

    // If b is zero, the output reduces to a + c.
    check_b_zero_reduces_to_a_plus_c: assert property (
        @(posedge clk) disable iff (1'b0)
        (b == '0) |-> (o == (a + c))
    );

    // If c is zero, the output reduces to a + b.
    check_c_zero_reduces_to_a_plus_b: assert property (
        @(posedge clk) disable iff (1'b0)
        (c == '0) |-> (o == (a + b))
    );

endmodule