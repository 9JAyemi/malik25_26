module top_module_assertions (
    input logic clk,
    input logic reset,
    input logic signed [7:0] A,
    input logic signed [7:0] B,
    input logic signed [3:0] C,
    input logic select,
    input logic signed [3:0] D
);

    // select=0 chooses the low nibble of the sum.
    check_select_low_uses_sum_low_nibble: assert property (
        @(posedge clk) disable iff (reset)
        (select == 1'b0) |-> (D == (((A * B) + C)[3:0]))
    );

    // select=1 chooses the upper nibble of the sum.
    check_select_high_uses_sum_high_nibble: assert property (
        @(posedge clk) disable iff (reset)
        (select == 1'b1) |-> (D == (((A * B) + C)[7:4]))
    );

    // With C=0, select=0 returns the low nibble of the product.
    check_zero_c_low_nibble_is_product: assert property (
        @(posedge clk) disable iff (reset)
        ((C == 4'sd0) && (select == 1'b0)) |-> (D == ((A * B)[3:0]))
    );

    // With C=0, select=1 returns the upper nibble of the product.
    check_zero_c_high_nibble_is_product: assert property (
        @(posedge clk) disable iff (reset)
        ((C == 4'sd0) && (select == 1'b1)) |-> (D == ((A * B)[7:4]))
    );

    // If either multiplier input is zero, select=0 returns C directly.
    check_zero_product_low_nibble_matches_c: assert property (
        @(posedge clk) disable iff (reset)
        (((A == 8'sd0) || (B == 8'sd0)) && (select == 1'b0)) |-> (D == C)
    );

    // If either multiplier input is zero, select=1 returns C sign extension.
    check_zero_product_high_nibble_is_c_sign_extension: assert property (
        @(posedge clk) disable iff (reset)
        (((A == 8'sd0) || (B == 8'sd0)) && (select == 1'b1)) |-> (D == {4{C[3]}})
    );

endmodule