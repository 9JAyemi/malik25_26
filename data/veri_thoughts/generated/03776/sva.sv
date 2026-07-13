module top_module_assertions (
    input logic clk,
    input logic reset,
    input logic [3:0] binary,
    input logic [3:0] bit_0,
    input logic [3:0] bit_1,
    input logic [3:0] bit_2,
    input logic [3:0] bit_3,
    input logic [3:0] sum
);

    // bit_0 and bit_1 are the low and high nibbles of binary squared.
    check_square_split: assert property (
        @(posedge clk) disable iff (reset)
        {bit_1, bit_0} == ({4'b0000, binary} * {4'b0000, binary})
    );

    // sum is the low 4 bits of bit_1 plus bit_2.
    check_sum_from_high_nibble_and_count: assert property (
        @(posedge clk) disable iff (reset)
        {1'b0, sum} == (({1'b0, bit_1} + {1'b0, bit_2}) & 5'h0F)
    );

    // bit_3 directly mirrors sum.
    check_bit3_matches_sum: assert property (
        @(posedge clk) disable iff (reset)
        bit_3 == sum
    );

    // A reset edge clears the observed counter output by the next clock.
    check_reset_clears_count: assert property (
        @(posedge clk)
        reset |=> bit_2 == 4'b0000
    );

    // After reset, the cleared count makes sum and bit_3 match bit_1.
    check_reset_aligns_sum_with_high_nibble: assert property (
        @(posedge clk)
        reset |=> (sum == bit_1) && (bit_3 == bit_1)
    );

    // When not in reset, the counter output rotates each clock.
    check_count_rotates: assert property (
        @(posedge clk) disable iff (reset)
        1'b1 |=> bit_2 == {$past(bit_2[2:0]), $past(bit_2[3])}
    );

    // Once the counter output is zero, it stays zero on active clocks.
    check_zero_count_is_sticky: assert property (
        @(posedge clk) disable iff (reset)
        bit_2 == 4'b0000 |=> bit_2 == 4'b0000
    );

endmodule