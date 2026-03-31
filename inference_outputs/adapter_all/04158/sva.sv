module binary_add_sub_sva (
    input logic [3:0] A,
    input logic [3:0] B,
    input logic       mode,
    input logic [3:0] Y
);

    // In add mode, Y must equal A plus B.
    check_add_mode_result: assert property (
        @($global_clock) (mode == 1'b0) |-> (Y == (A + B))
    );

    // In subtract mode, Y must equal A plus the two's complement of B.
    check_sub_mode_result: assert property (
        @($global_clock) (mode == 1'b1) |-> (Y == (A + ((~B) + 4'b0001)))
    );

    // In subtract mode, adding B back to Y must recover A.
    check_sub_mode_inverse: assert property (
        @($global_clock) (mode == 1'b1) |-> ((Y + B) == A)
    );

    // With zero B, Y must pass A through regardless of mode.
    check_zero_b_passthrough: assert property (
        @($global_clock) (B == 4'b0000) |-> (Y == A)
    );

    // In add mode, zero A must pass B through.
    check_add_zero_a_passthrough: assert property (
        @($global_clock) ((mode == 1'b0) && (A == 4'b0000)) |-> (Y == B)
    );

    // In subtract mode, zero A must produce the two's complement of B.
    check_sub_zero_a_twos_complement: assert property (
        @($global_clock) ((mode == 1'b1) && (A == 4'b0000)) |-> (Y == ((~B) + 4'b0001))
    );

    // In subtract mode, equal operands must cancel to zero.
    check_sub_equal_operands_zero: assert property (
        @($global_clock) ((mode == 1'b1) && (A == B)) |-> (Y == 4'b0000)
    );

endmodule