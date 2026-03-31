module bitwise_or_twos_complement_sva (
    input logic [3:0] a,
    input logic [3:0] b,
    input logic [3:0] out
);

    // Output matches the two's complement of a | b.
    check_out_matches_twos_complement_of_or: assert property (
        @($global_clock) out == ~((a | b) & 4'hF) + 4'h1
    );

    // Output is the bitwise inverse of the OR result plus one.
    check_out_is_inverse_plus_one_of_or: assert property (
        @($global_clock) out == ~((a | b) & 4'hF) + 4'h1
    );

    // If a is zero, output is the two's complement of b.
    check_zero_a_behavior: assert property (
        @($global_clock) (a == 4'h0) |-> (out == ~b + 4'h1)
    );

    // If b is zero, output is the two's complement of a.
    check_zero_b_behavior: assert property (
        @($global_clock) (b == 4'h0) |-> (out == ~a + 4'h1)
    );

    // If a and b are equal, output is zero.
    check_equal_inputs_zero_output: assert property (
        @($global_clock) (a == b) |-> (out == 4'h0)
    );

    // If a is all ones, output is the two's complement of b.
    check_all_ones_a_behavior: assert property (
        @($global_clock) (a == 4'hF) |-> (out == ~b + 4'h1)
    );

    // If b is all ones, output is the two's complement of a.
    check_all_ones_b_behavior: assert property (
        @($global_clock) (b == 4'hF) |-> (out == ~a + 4'h1)
    );

    // If a is all zeros, output is the two's complement of b.
    check_all_zeros_a_behavior: assert property (
        @($global_clock) (a == 4'h0) |-> (out == ~b + 4'h1)
    );

    // If b is all zeros, output is the two's complement of a.
    check_all_zeros_b_behavior: assert property (
        @($global_clock) (b == 4'h0) |-> (out == ~a + 4'h1)
    );

    // If a is zero and b is all ones, output is zero.
    check_zero_a_all_ones_b_behavior: assert property (
        @($global_clock) ((a == 4'h0) && (b == 4'hF)) |-> (out == 4'h0)
    );

    // If a is all ones and b is zero, output is zero.
    check_all_ones_a_zero_b_behavior: assert property (
        @($global_clock) ((a == 4'hF) && (b == 4'h0)) |-> (out == 4'h0)
    );

endmodule