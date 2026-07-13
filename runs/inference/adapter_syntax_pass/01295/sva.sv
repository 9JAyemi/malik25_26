module bitwise_or_twos_complement_sva (
    input logic [3:0] a,
    input logic [3:0] b,
    input logic [3:0] out
);

    // out is the two's complement of the bitwise OR of a and b.
    check_out_matches_twos_complement_of_or: assert property (
        @($global_clock) out == (~((a | b) + 4'd1))
    );

    // out is the two's complement of a when b is zero.
    check_out_matches_twos_complement_of_a_when_b_zero: assert property (
        @($global_clock) (b == 4'd0) |-> (out == (~a + 4'd1))
    );

    // out is the two's complement of b when a is zero.
    check_out_matches_twos_complement_of_b_when_a_zero: assert property (
        @($global_clock) (a == 4'd0) |-> (out == (~b + 4'd1))
    );

    // out is zero when the OR result is all ones.
    check_out_zero_when_or_result_all_ones: assert property (
        @($global_clock) ((a | b) == 4'hF) |-> (out == 4'h0)
    );

    // out is all ones when the OR result is all zeros.
    check_out_all_ones_when_or_result_all_zeros: assert property (
        @($global_clock) ((a | b) == 4'h0) |-> (out == 4'hF)
    );

    // out is the bitwise NOT of a when b is all ones.
    check_out_is_not_a_when_b_all_ones: assert property (
        @($global_clock) (b == 4'hF) |-> (out == ~a)
    );

    // out is the bitwise NOT of b when a is all ones.
    check_out_is_not_b_when_a_all_ones: assert property (
        @($global_clock) (a == 4'hF) |-> (out == ~b)
    );

endmodule