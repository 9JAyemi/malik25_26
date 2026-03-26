module adder4_assertions(
    input logic [3:0] a,
    input logic [3:0] b,
    input logic [3:0] sum
);

    // Sum matches a+b modulo 16.
    check_sum_mod16: assert property (
        @($global_clock) {1'b0, sum} == (({1'b0, a} + {1'b0, b}) & 5'h0f)
    );

    // No-overflow additions pass through unchanged.
    check_no_overflow_result: assert property (
        @($global_clock) (({1'b0, a} + {1'b0, b}) <= 5'd15) |-> ({1'b0, sum} == ({1'b0, a} + {1'b0, b}))
    );

    // Overflow additions wrap by subtracting 16.
    check_overflow_wrap_result: assert property (
        @($global_clock) (({1'b0, a} + {1'b0, b}) > 5'd15) |-> ({1'b0, sum} == (({1'b0, a} + {1'b0, b}) - 5'd16))
    );

    // Zero on a leaves b unchanged at the output.
    check_zero_a_passthrough: assert property (
        @($global_clock) (a == 4'h0) |-> (sum == b)
    );

    // Zero on b leaves a unchanged at the output.
    check_zero_b_passthrough: assert property (
        @($global_clock) (b == 4'h0) |-> (sum == a)
    );

    // A full sum of 15 is preserved.
    check_fullsum_fifteen: assert property (
        @($global_clock) (({1'b0, a} + {1'b0, b}) == 5'd15) |-> (sum == 4'hf)
    );

    // A full sum of 16 wraps to zero.
    check_fullsum_sixteen_wrap: assert property (
        @($global_clock) (({1'b0, a} + {1'b0, b}) == 5'd16) |-> (sum == 4'h0)
    );

    // Zero plus zero produces zero.
    check_zero_plus_zero: assert property (
        @($global_clock) (a == 4'h0 && b == 4'h0) |-> (sum == 4'h0)
    );

    // Fifteen plus fifteen wraps to fourteen.
    check_max_plus_max_wrap: assert property (
        @($global_clock) (a == 4'hf && b == 4'hf) |-> (sum == 4'he)
    );

endmodule