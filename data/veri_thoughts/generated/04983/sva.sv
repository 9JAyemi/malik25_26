module binary_adder_sva (
    input logic clk,
    input logic [3:0] a,
    input logic [3:0] b,
    input logic [3:0] sum
);

    // Sum is the low 4 bits of the full addition.
    check_sum_matches_low_nibble: assert property (
        @(posedge clk) {1'b0, sum} == (({1'b0, a} + {1'b0, b}) & 5'h0f)
    );

    // When there is no overflow, sum matches the full result.
    check_sum_no_overflow: assert property (
        @(posedge clk) (({1'b0, a} + {1'b0, b}) <= 5'd15) |-> ({1'b0, sum} == ({1'b0, a} + {1'b0, b}))
    );

    // When there is overflow, sum wraps modulo 16.
    check_sum_wraps_on_overflow: assert property (
        @(posedge clk) (({1'b0, a} + {1'b0, b}) > 5'd15) |-> ({1'b0, sum} == (({1'b0, a} + {1'b0, b}) - 5'd16))
    );

    // Adding zero on a leaves b unchanged.
    check_zero_a_identity: assert property (
        @(posedge clk) (a == 4'd0) |-> (sum == b)
    );

    // Adding zero on b leaves a unchanged.
    check_zero_b_identity: assert property (
        @(posedge clk) (b == 4'd0) |-> (sum == a)
    );

    // The least significant sum bit is the XOR of operand LSBs.
    check_lsb_xor: assert property (
        @(posedge clk) sum[0] == (a[0] ^ b[0])
    );

endmodule