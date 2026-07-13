module zbroji_sva (
    input logic [31:0] a,
    input logic [31:0] b,
    input logic [31:0] sum
);

    // Sum must always equal the 32-bit addition of a and b.
    check_sum_matches_addition: assert property (
        @($global_clock) sum == (a + b)
    );

    // Adding zero on the left must pass b through unchanged.
    check_left_zero_identity: assert property (
        @($global_clock) (a == 32'h00000000) |-> (sum == b)
    );

    // Adding zero on the right must pass a through unchanged.
    check_right_zero_identity: assert property (
        @($global_clock) (b == 32'h00000000) |-> (sum == a)
    );

    // If both inputs stay the same, the sum must stay the same.
    check_stable_inputs_keep_sum_stable: assert property (
        @($global_clock) ($stable(a) && $stable(b)) |-> $stable(sum)
    );

    // With b unchanged, the change in sum must match the change in a.
    check_a_delta_propagates_to_sum: assert property (
        @($global_clock) ($stable(b) && !$stable(a)) |-> ((sum - $past(sum)) == (a - $past(a)))
    );

    // With a unchanged, the change in sum must match the change in b.
    check_b_delta_propagates_to_sum: assert property (
        @($global_clock) ($stable(a) && !$stable(b)) |-> ((sum - $past(sum)) == (b - $past(b)))
    );

endmodule