module addition_4bit_sva (
    input logic        clk,
    input logic [3:0]  a,
    input logic [3:0]  b,
    input logic [3:0]  sum
);

    // sum must equal the 4-bit addition of a and b.
    check_sum_matches_4bit_add: assert property (
        @(posedge clk) sum == (a + b)
    );

    // When the mathematical sum is 15 or less, sum matches it exactly.
    check_sum_no_wrap: assert property (
        @(posedge clk) (({1'b0, a} + {1'b0, b}) <= 5'd15) |-> (sum == ({1'b0, a} + {1'b0, b}))
    );

    // When the mathematical sum exceeds 15, sum wraps modulo 16.
    check_sum_wraps_mod_16: assert property (
        @(posedge clk) (({1'b0, a} + {1'b0, b}) >= 5'd16) |-> (sum == (({1'b0, a} + {1'b0, b}) - 5'd16))
    );

    // Adding zero on a leaves b unchanged at the output.
    check_zero_a_passthrough: assert property (
        @(posedge clk) (a == 4'd0) |-> (sum == b)
    );

    // Adding zero on b leaves a unchanged at the output.
    check_zero_b_passthrough: assert property (
        @(posedge clk) (b == 4'd0) |-> (sum == a)
    );

endmodule