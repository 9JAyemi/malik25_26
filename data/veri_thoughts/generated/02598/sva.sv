module arith_sva (
    input logic clk,
    input logic [7:0] a,
    input logic [7:0] b,
    input logic [7:0] sum,
    input logic [7:0] diff,
    input logic [7:0] prod
);
    // sum matches 8-bit addition of a and b
    check_sum_equals_addition: assert property (
        @(posedge clk) sum == (a + b)
    );

    // diff matches 8-bit subtraction a - b
    check_diff_equals_subtraction: assert property (
        @(posedge clk) diff == (a - b)
    );

    // prod matches low 8 bits of a * b
    check_prod_equals_mult_low8: assert property (
        @(posedge clk) prod == (a * b)[7:0]
    );

    // sum - b recovers a (mod 256)
    check_sum_minus_b_recovers_a: assert property (
        @(posedge clk) (sum - b) == a
    );

    // diff + b recovers a (mod 256)
    check_diff_plus_b_recovers_a: assert property (
        @(posedge clk) (diff + b) == a
    );

    // If a is zero, product is zero
    check_prod_zero_when_a_zero: assert property (
        @(posedge clk) (a == 8'h00) |-> (prod == 8'h00)
    );

    // If b is zero, product is zero
    check_prod_zero_when_b_zero: assert property (
        @(posedge clk) (b == 8'h00) |-> (prod == 8'h00)
    );

    // (sum - diff) equals 2*b (mod 256)
    check_sum_minus_diff_is_2b: assert property (
        @(posedge clk) (sum - diff) == (b << 1)
    );

    // (sum + diff) equals 2*a (mod 256)
    check_sum_plus_diff_is_2a: assert property (
        @(posedge clk) (sum + diff) == (a << 1)
    );

    // Equal inputs imply sum is 2*a and diff is 0
    check_equal_inputs_implications: assert property (
        @(posedge clk) (a == b) |-> ((sum == (a << 1)) && (diff == 8'h00))
    );
endmodule