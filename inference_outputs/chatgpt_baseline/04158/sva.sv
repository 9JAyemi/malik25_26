module binary_add_sub_sva (
    input logic [3:0] A,
    input logic [3:0] B,
    input logic mode,
    input logic [3:0] Y
);

    // In add mode, Y is the 4-bit sum of A and B.
    check_add_mode_result: assert property (
        @($global_clock)
        (mode == 1'b0) |-> (Y == (A + B))
    );

    // In subtract mode, Y is A plus the 2's complement of B.
    check_sub_mode_result: assert property (
        @($global_clock)
        (mode == 1'b1) |-> (Y == (A + ((~B) + 4'b0001)))
    );

    // In add mode, zero on A passes B through to Y.
    check_add_zero_a_passthrough: assert property (
        @($global_clock)
        ((mode == 1'b0) && (A == 4'b0000)) |-> (Y == B)
    );

    // In add mode, zero on B passes A through to Y.
    check_add_zero_b_passthrough: assert property (
        @($global_clock)
        ((mode == 1'b0) && (B == 4'b0000)) |-> (Y == A)
    );

    // In subtract mode, zero on B leaves Y equal to A.
    check_sub_zero_b_passthrough: assert property (
        @($global_clock)
        ((mode == 1'b1) && (B == 4'b0000)) |-> (Y == A)
    );

    // In subtract mode, equal operands produce zero.
    check_sub_equal_operands_zero: assert property (
        @($global_clock)
        ((mode == 1'b1) && (A == B)) |-> (Y == 4'b0000)
    );

    // In subtract mode, zero on A yields the 2's complement of B.
    check_sub_zero_a_twos_complement: assert property (
        @($global_clock)
        ((mode == 1'b1) && (A == 4'b0000)) |-> (Y == ((~B) + 4'b0001))
    );

    // With both operands zero, Y is zero in either mode.
    check_zero_inputs_zero_output: assert property (
        @($global_clock)
        ((A == 4'b0000) && (B == 4'b0000)) |-> (Y == 4'b0000)
    );

endmodule