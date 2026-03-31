module adder_sva (
    input logic [3:0] A,
    input logic [3:0] B,
    input logic [3:0] C,
    input logic       CO
);

    // C is the low 4 bits of A plus B.
    check_c_matches_low_sum: assert property (
        @($global_clock) C == (A + B)
    );

    // CO is the carry-out bit of the 4-bit addition.
    check_co_matches_carry: assert property (
        @($global_clock) CO == (({1'b0, A} + {1'b0, B}) >= 5'd16)
    );

    // The concatenated result matches the 5-bit addition.
    check_concatenated_result: assert property (
        @($global_clock) {CO, C} == ({1'b0, A} + {1'b0, B})
    );

    // Zero on A passes B through with no carry.
    check_zero_a_passthrough: assert property (
        @($global_clock) (A == 4'h0) |-> ((C == B) && (CO == 1'b0))
    );

    // Zero on B passes A through with no carry.
    check_zero_b_passthrough: assert property (
        @($global_clock) (B == 4'h0) |-> ((C == A) && (CO == 1'b0))
    );

    // 4'hF plus 4'h1 wraps to 4'h0 with carry-out set.
    check_f_plus_one_wrap: assert property (
        @($global_clock) ((A == 4'hF) && (B == 4'h1)) |-> ((C == 4'h0) && (CO == 1'b1))
    );

endmodule