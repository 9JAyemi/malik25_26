module top_module_sva (
    input logic clk,
    input logic signed [15:0] a,
    input logic signed [15:0] b,
    input logic signed [31:0] product_sum,
    input logic [15:0] a_unsigned,
    input logic [15:0] b_unsigned,
    input logic [15:0] product_low,
    input logic [15:0] product_high
);

    // No RTL clock or reset exists; clk is an external sampling clock.
    
    // a_unsigned is the truncated 16-bit copy of a.
    check_a_unsigned_tracks_a: assert property (
        @(posedge clk) a_unsigned == a[15:0]
    );

    // b_unsigned is the truncated 16-bit copy of b.
    check_b_unsigned_tracks_b: assert property (
        @(posedge clk) b_unsigned == b[15:0]
    );

    // product_low matches the low-byte 8x8 multiplication.
    check_product_low_matches_low_byte_mul: assert property (
        @(posedge clk) product_low == (a_unsigned[7:0] * b_unsigned[7:0])
    );

    // product_high matches the high-byte 8x8 multiplication.
    check_product_high_matches_high_byte_mul: assert property (
        @(posedge clk) product_high == (a_unsigned[15:8] * b_unsigned[15:8])
    );

    // The low half of product_sum comes directly from product_low.
    check_product_sum_low_half_matches_product_low: assert property (
        @(posedge clk) product_sum[15:0] == product_low
    );

    // The high half of product_sum is the sum of both partial products.
    check_product_sum_high_half_matches_partial_sum: assert property (
        @(posedge clk) product_sum[31:16] == (product_high + product_low)
    );

    // The full output is assembled from the partial-sum upper half and product_low.
    check_product_sum_full_assembly: assert property (
        @(posedge clk) product_sum == {(product_high + product_low), product_low}
    );

    // The full output matches the direct byte-sliced arithmetic formula.
    check_product_sum_matches_direct_formula: assert property (
        @(posedge clk) product_sum == {((a[15:8] * b[15:8]) + (a[7:0] * b[7:0])), (a[7:0] * b[7:0])}
    );

    // A zero input operand forces the complete output to zero.
    check_zero_operand_forces_zero_output: assert property (
        @(posedge clk) ((a == 16'sh0000) || (b == 16'sh0000)) |-> (product_sum == 32'h00000000)
    );

    // If the low-byte multiply is zero, the upper half reduces to product_high.
    check_zero_low_byte_reduces_upper_to_product_high: assert property (
        @(posedge clk) ((a[7:0] == 8'h00) || (b[7:0] == 8'h00)) |->
            ((product_sum[15:0] == 16'h0000) && (product_sum[31:16] == product_high))
    );

    // If the high-byte multiply is zero, both halves carry the low-byte product.
    check_zero_high_byte_makes_halves_equal: assert property (
        @(posedge clk) ((a[15:8] == 8'h00) || (b[15:8] == 8'h00)) |->
            (product_sum[31:16] == product_sum[15:0])
    );

endmodule