module adder_4bit_sva(
    input logic [3:0] a,
    input logic [3:0] b,
    input logic [3:0] sum
);

    // Sum must match the 4-bit addition of the inputs.
    check_sum_matches_addition: assert property (
        @($global_clock) sum == (a + b)
    );

    // Stable inputs must keep the sum stable.
    check_stable_inputs_keep_sum_stable: assert property (
        @($global_clock) ($stable(a) && $stable(b)) |-> $stable(sum)
    );

    // Adding zero on b must pass a through to sum.
    check_zero_b_passthrough: assert property (
        @($global_clock) (b == 4'h0) |-> (sum == a)
    );

    // Adding zero on a must pass b through to sum.
    check_zero_a_passthrough: assert property (
        @($global_clock) (a == 4'h0) |-> (sum == b)
    );

    // The least significant sum bit must be the xor of input LSBs.
    check_lsb_sum_behavior: assert property (
        @($global_clock) sum[0] == (a[0] ^ b[0])
    );

endmodule