module xor_32_sva (
    input logic [31:0] a,
    input logic [31:0] b,
    input logic [31:0] out
);

    // No RTL clock/reset; sample this combinational logic on the formal global clock.

    // out must always equal the bitwise XOR of a and b.
    check_out_matches_bitwise_xor: assert property (
        @($global_clock) out == (a ^ b)
    );

    // If b is zero, out must pass through a unchanged.
    check_b_zero_passthrough: assert property (
        @($global_clock) (b == 32'h0000_0000) |-> (out == a)
    );

    // If a is zero, out must pass through b unchanged.
    check_a_zero_passthrough: assert property (
        @($global_clock) (a == 32'h0000_0000) |-> (out == b)
    );

    // Equal inputs must produce a zero output.
    check_equal_inputs_zero_output: assert property (
        @($global_clock) (a == b) |-> (out == 32'h0000_0000)
    );

    // If b is all ones, out must be the bitwise inverse of a.
    check_b_all_ones_inverts_a: assert property (
        @($global_clock) (b == 32'hFFFF_FFFF) |-> (out == ~a)
    );

    // If a is all ones, out must be the bitwise inverse of b.
    check_a_all_ones_inverts_b: assert property (
        @($global_clock) (a == 32'hFFFF_FFFF) |-> (out == ~b)
    );

    // XORing out with b must recover a.
    check_output_with_b_recovers_a: assert property (
        @($global_clock) ((out ^ b) == a)
    );

    // XORing out with a must recover b.
    check_output_with_a_recovers_b: assert property (
        @($global_clock) ((out ^ a) == b)
    );

endmodule