module bitwise_and_sva (
    input logic [3:0] a,
    input logic [3:0] b,
    input logic [3:0] result
);

    // Result must equal the bitwise AND of a and b.
    check_result_matches_and: assert property (
        @($global_clock) result == (a & b)
    );

    // Result bit 0 must equal a[0] AND b[0].
    check_result_bit0: assert property (
        @($global_clock) result[0] == (a[0] & b[0])
    );

    // Result bit 1 must equal a[1] AND b[1].
    check_result_bit1: assert property (
        @($global_clock) result[1] == (a[1] & b[1])
    );

    // Result bit 2 must equal a[2] AND b[2].
    check_result_bit2: assert property (
        @($global_clock) result[2] == (a[2] & b[2])
    );

    // Result bit 3 must equal a[3] AND b[3].
    check_result_bit3: assert property (
        @($global_clock) result[3] == (a[3] & b[3])
    );

    // If a is all zeros, result must be all zeros.
    check_zero_a_forces_zero_result: assert property (
        @($global_clock) (a == 4'b0000) |-> (result == 4'b0000)
    );

    // If b is all zeros, result must be all zeros.
    check_zero_b_forces_zero_result: assert property (
        @($global_clock) (b == 4'b0000) |-> (result == 4'b0000)
    );

    // If a is all ones, result must equal b.
    check_all_ones_a_passes_b: assert property (
        @($global_clock) (a == 4'b1111) |-> (result == b)
    );

    // If b is all ones, result must equal a.
    check_all_ones_b_passes_a: assert property (
        @($global_clock) (b == 4'b1111) |-> (result == a)
    );

    // If a and b are equal, result must equal a (and b).
    check_equal_inputs_pass_through: assert property (
        @($global_clock) (a == b) |-> (result == a)
    );

endmodule