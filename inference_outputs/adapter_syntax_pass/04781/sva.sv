module zbroji_sva (
    input logic [31:0] a,
    input logic [31:0] b,
    input logic [31:0] sum
);

    // sum must equal the 32-bit addition of a and b.
    check_sum_matches_addition: assert property (
        @($global_clock) sum == (a + b)
    );

    // The least-significant bit of sum must match the least-significant bit of the addition.
    check_lsb_matches_addition: assert property (
        @($global_clock) sum[0] == (a[0] ^ b[0])
    );

    // Adding zero on b must pass a through to sum.
    check_zero_b_passthrough: assert property (
        @($global_clock) (b == 32'h00000000) |-> (sum == a)
    );

    // Adding zero on a must pass b through to sum.
    check_zero_a_passthrough: assert property (
        @($global_clock) (a == 32'h00000000) |-> (sum == b)
    );

    // Adding equal 16-bit upper halves must preserve the lower 16 bits.
    check_upper_half_preserved_when_upper_equal: assert property (
        @($global_clock) ((a[31:16] == b[31:16]) && (a[15:0] != 16'h0000) && (b[15:0] != 16'h0000)) |-> ((sum[31:16] == a[31:16]) && (sum[15:0] == (a[15:0] + b[15:0])))
    );

endmodule