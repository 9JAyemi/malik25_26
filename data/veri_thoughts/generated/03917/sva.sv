module binary_adder_sva (
    input logic clk,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic [3:0] S
);

    // When the 5-bit sum is 15 or less, S matches the exact sum.
    check_sum_no_overflow: assert property (
        @(posedge clk)
        (({1'b0, A} + {1'b0, B}) <= 5'd15) |-> ({1'b0, S} == ({1'b0, A} + {1'b0, B}))
    );

    // When the 5-bit sum exceeds 15, S wraps to the low 4 bits.
    check_sum_overflow_wrap: assert property (
        @(posedge clk)
        (({1'b0, A} + {1'b0, B}) > 5'd15) |-> ({1'b0, S} == (({1'b0, A} + {1'b0, B}) - 5'd16))
    );

    // A zero B input leaves the output equal to A.
    check_b_zero_identity: assert property (
        @(posedge clk)
        (B == 4'd0) |-> (S == A)
    );

    // A zero A input leaves the output equal to B.
    check_a_zero_identity: assert property (
        @(posedge clk)
        (A == 4'd0) |-> (S == B)
    );

    // The largest non-overflowing sum passes through unchanged.
    check_boundary_sum_fifteen: assert property (
        @(posedge clk)
        (({1'b0, A} + {1'b0, B}) == 5'd15) |-> (S == 4'd15)
    );

    // The first overflowing sum wraps to zero.
    check_boundary_sum_sixteen: assert property (
        @(posedge clk)
        (({1'b0, A} + {1'b0, B}) == 5'd16) |-> (S == 4'd0)
    );

    // Stable inputs keep the sampled output stable.
    check_stable_inputs_stable_output: assert property (
        @(posedge clk)
        ($stable(A) && $stable(B)) |-> $stable(S)
    );

endmodule