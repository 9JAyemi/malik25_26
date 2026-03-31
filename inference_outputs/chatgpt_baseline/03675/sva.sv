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

generate
if (SIGN_EXT == 1'b0) begin : gen_no_sign_ext
    // Output matches the direct ternary addition branch.
    check_sum_matches_no_sign_ext: assert property (
        @(posedge clk) o == (a + b + c)
    );

    // The upper two bits are zero in the non-sign-extended branch.
    check_upper_bits_zero_no_sign_ext: assert property (
        @(posedge clk) o[WIDTH+1:WIDTH] == 2'b00
    );

    // Zero inputs produce a zero output.
    check_zero_output_no_sign_ext: assert property (
        @(posedge clk) ((a == '0) && (b == '0) && (c == '0)) |-> (o == '0)
    );

    // With only a present, o is zero-extended a.
    check_a_passthrough_no_sign_ext: assert property (
        @(posedge clk) ((b == '0) && (c == '0)) |-> (o == {{2{1'b0}}, a})
    );

    // With only b present, o is zero-extended b.
    check_b_passthrough_no_sign_ext: assert property (
        @(posedge clk) ((a == '0) && (c == '0)) |-> (o == {{2{1'b0}}, b})
    );

    // With only c present, o is zero-extended c.
    check_c_passthrough_no_sign_ext: assert property (
        @(posedge clk) ((a == '0) && (b == '0)) |-> (o == {{2{1'b0}}, c})
    );
end else begin : gen_sign_ext
    // Output matches the sign-extended ternary addition branch.
    check_sum_matches_sign_ext: assert property (
        @(posedge clk) o == ({a[WIDTH-1], a[WIDTH-1], a} +
                             {b[WIDTH-1], b[WIDTH-1], b} +
                             {c[WIDTH-1], c[WIDTH-1], c})
    );

    // Zero inputs produce a zero output.
    check_zero_output_sign_ext: assert property (
        @(posedge clk) ((a == '0) && (b == '0) && (c == '0)) |-> (o == '0)
    );

    // With only a present, o is sign-extended a.
    check_a_passthrough_sign_ext: assert property (
        @(posedge clk) ((b == '0) && (c == '0)) |-> (o == {a[WIDTH-1], a[WIDTH-1], a})
    );

    // With only b present, o is sign-extended b.
    check_b_passthrough_sign_ext: assert property (
        @(posedge clk) ((a == '0) && (c == '0)) |-> (o == {b[WIDTH-1], b[WIDTH-1], b})
    );

    // With only c present, o is sign-extended c.
    check_c_passthrough_sign_ext: assert property (
        @(posedge clk) ((a == '0) && (b == '0)) |-> (o == {c[WIDTH-1], c[WIDTH-1], c})
    );

    // When a is zero, the output reduces to the sign-extended sum of b and c.
    check_bc_reduction_sign_ext: assert property (
        @(posedge clk) (a == '0) |-> (o == ({b[WIDTH-1], b[WIDTH-1], b} +
                                            {c[WIDTH-1], c[WIDTH-1], c}))
    );
end
endgenerate

endmodule