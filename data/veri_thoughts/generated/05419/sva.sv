module bitwise_xor_sva(
    input logic [31:0] a,
    input logic [31:0] b,
    input logic [31:0] result
);

    // No RTL clock or reset; sample combinational behavior on the global clock.

    // Result must always equal the bitwise XOR of a and b.
    check_result_is_xor: assert property (
        @($global_clock) result == (a ^ b)
    );

    // Equal inputs must produce an all-zero result.
    check_equal_inputs_zero_result: assert property (
        @($global_clock) (a == b) |-> (result == 32'h00000000)
    );

    // A zero value on a must pass b through unchanged.
    check_zero_a_passthrough_b: assert property (
        @($global_clock) (a == 32'h00000000) |-> (result == b)
    );

    // A zero value on b must pass a through unchanged.
    check_zero_b_passthrough_a: assert property (
        @($global_clock) (b == 32'h00000000) |-> (result == a)
    );

    // All ones on a must invert b.
    check_all_ones_a_inverts_b: assert property (
        @($global_clock) (a == 32'hFFFFFFFF) |-> (result == ~b)
    );

    // All ones on b must invert a.
    check_all_ones_b_inverts_a: assert property (
        @($global_clock) (b == 32'hFFFFFFFF) |-> (result == ~a)
    );

    // XORing result with a must recover b.
    check_result_xor_a_recovers_b: assert property (
        @($global_clock) (result ^ a) == b
    );

    // XORing result with b must recover a.
    check_result_xor_b_recovers_a: assert property (
        @($global_clock) (result ^ b) == a
    );

endmodule