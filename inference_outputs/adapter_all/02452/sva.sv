module top_module_sva (
    input logic        clk,
    input logic [15:0] in,
    input logic [7:0]  a,
    input logic [7:0]  b,
    input logic [7:0]  out
);

    // Output matches the low byte of the product of a and b.
    check_out_matches_product_low_byte: assert property (
        @(posedge clk) out == (a * b)[7:0]
    );

    // If either multiplicand is zero, the output is zero.
    check_zero_multiplicand_gives_zero: assert property (
        @(posedge clk) ((a == 8'h00) || (b == 8'h00)) |-> (out == 8'h00)
    );

    // If either multiplicand is 1, the output equals the other multiplicand.
    check_one_multiplicand_passthrough: assert property (
        @(posedge clk) ((a == 8'h01) || (b == 8'h01)) |-> (out == (a ^ b))
    );

    // Multiplication by 8 produces a left shift by 3.
    check_multiply_by_eight: assert property (
        @(posedge clk) (b == 8'h08) |-> (out == (a << 3))
    );

    // Multiplication by 16 produces a left shift by 4.
    check_multiply_by_sixteen: assert property (
        @(posedge clk) (b == 8'h10) |-> (out == (a << 4))
    );

    // Multiplication by 32 produces a left shift by 5.
    check_multiply_by_thirty_two: assert property (
        @(posedge clk) (b == 8'h20) |-> (out == (a << 5))
    );

    // Multiplication by 64 produces a left shift by 6.
    check_multiply_by_sixty_four: assert property (
        @(posedge clk) (b == 8'h40) |-> (out == (a << 6))
    );

    // Multiplication by 128 produces a left shift by 7.
    check_multiply_by_one_twenty_eight: assert property (
        @(posedge clk) (b == 8'h80) |-> (out == (a << 7))
    );

    // Multiplication by 255 produces a left shift by 7.
    check_multiply_by_two_fifty_five: assert property (
        @(posedge clk) (b == 8'hFF) |-> (out == (a << 7))
    );

    // Multiplication by 256 wraps the low byte to zero.
    check_multiply_by_two_fifty_six: assert property (
        @(posedge clk) (b == 8'h01) |-> (out == 8'h00)
    );

    // Multiplication by 512 wraps the low byte to zero.
    check_multiply_by_five_hundred_twelve: assert property (
        @(posedge clk) (b == 8'h02) |-> (out == 8'h00)
    );

    // Multiplication by 1024 wraps the low byte to zero.
    check_multiply_by_one_thousand_twenty_four: assert property (
        @(posedge clk) (b == 8'h04) |-> (out == 8'h00)
    );

    // Multiplication by 2048 wraps the low byte to zero.
    check_multiply_by_two_thousand_fifty_six: assert property (
        @(posedge clk) (b == 8'h08) |-> (out == 8'h00)
    );

    // Multiplication by 4096 wraps the low byte to zero.
    check_multiply_by_four_thousand_eighty_eight: assert property (
        @(posedge clk) (b == 8'h10) |-> (out == 8'h00)
    );

    // Multiplication by 8192 wraps the low byte to zero.
    check_multiply_by_eight_thousand_one_hundred_ninety_two: assert property (
        @(posedge clk) (b == 8'h20) |-> (out == 8'h00)
    );

    // Multiplication by 16384 wraps the low byte to zero.
    check_multiply_by_sixteen_thousand_three_hundred_eighty_four: assert property (
        @(posedge clk) (b == 8'h40) |-> (out == 8'h00)
    );

    // Multiplication by 32768 wraps the low byte to zero.
    check_multiply_by_thirty_two_thousand_seven_hundred_sixty_eight: assert property (
        @(posedge clk) (b == 8'h80) |-> (out == 8'h00)
    );

    // Multiplication by 65535 wraps the low byte to zero.
    check_multiply_by_sixty_five_thousand_five_hundred_thirty_five: assert property (
        @(posedge clk) (b == 8'hFF) |-> (out == 8'h00)
    );

endmodule