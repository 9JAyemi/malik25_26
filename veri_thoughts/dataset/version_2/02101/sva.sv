module simple_calculator_sva (
    input logic clk,
    input logic signed [31:0] a,
    input logic signed [31:0] b,
    input logic [1:0] mode,
    input logic signed [31:0] sum,
    input logic signed [31:0] difference,
    input logic signed [31:0] product,
    input logic signed [31:0] quotient
);
    // In mode 00, sum is 32-bit truncated a+b; others are 0.
    check_mode00_sum_and_zeros: assert property (
        @(posedge clk)
        (mode == 2'b00) |-> (
            sum == $signed((($signed(a) + $signed(b))[31:0])) &&
            difference == 32'sd0 &&
            product == 32'sd0 &&
            quotient == 32'sd0
        )
    );

    // In mode 01, difference is 32-bit truncated a-b; others are 0.
    check_mode01_diff_and_zeros: assert property (
        @(posedge clk)
        (mode == 2'b01) |-> (
            sum == 32'sd0 &&
            difference == $signed((($signed(a) - $signed(b))[31:0])) &&
            product == 32'sd0 &&
            quotient == 32'sd0
        )
    );

    // In mode 10, product is 32-bit truncated a*b; others are 0.
    check_mode10_prod_and_zeros: assert property (
        @(posedge clk)
        (mode == 2'b10) |-> (
            sum == 32'sd0 &&
            difference == 32'sd0 &&
            product == $signed((($signed(a) * $signed(b))[31:0])) &&
            quotient == 32'sd0
        )
    );

    // In mode 11, non-selected outputs are 0.
    check_mode11_zeros: assert property (
        @(posedge clk)
        (mode == 2'b11) |-> (
            sum == 32'sd0 &&
            difference == 32'sd0 &&
            product == 32'sd0
        )
    );

    // In mode 11 with b!=0, quotient equals signed a/b.
    check_mode11_quotient_value: assert property (
        @(posedge clk)
        (mode == 2'b11 && b != 32'sd0) |-> (quotient == ($signed(a) / $signed(b)))
    );

    // When mode is not 00, sum must be 0.
    check_sum_zero_when_not_mode00: assert property (
        @(posedge clk)
        (mode != 2'b00) |-> (sum == 32'sd0)
    );

    // When mode is not 01, difference must be 0.
    check_difference_zero_when_not_mode01: assert property (
        @(posedge clk)
        (mode != 2'b01) |-> (difference == 32'sd0)
    );

    // When mode is not 10, product must be 0.
    check_product_zero_when_not_mode10: assert property (
        @(posedge clk)
        (mode != 2'b10) |-> (product == 32'sd0)
    );

    // When mode is not 11, quotient must be 0.
    check_quotient_zero_when_not_mode11: assert property (
        @(posedge clk)
        (mode != 2'b11) |-> (quotient == 32'sd0)
    );

    // At most one output is non-zero at any time.
    check_outputs_at_most_one_nonzero: assert property (
        @(posedge clk)
        !(
            (sum != 32'sd0 && difference != 32'sd0) ||
            (sum != 32'sd0 && product != 32'sd0) ||
            (sum != 32'sd0 && quotient != 32'sd0) ||
            (difference != 32'sd0 && product != 32'sd0) ||
            (difference != 32'sd0 && quotient != 32'sd0) ||
            (product != 32'sd0 && quotient != 32'sd0)
        )
    );
endmodule