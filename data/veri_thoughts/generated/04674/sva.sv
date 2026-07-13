module calculator_sva (
    input logic [3:0] A,
    input logic [3:0] B,
    input logic       mode,
    input logic [3:0] Y
);

    // No clock or reset exists in the RTL; assertions are sampled on $global_clock.
    // The design is purely combinational from A, B, and mode to Y.

    // In mode 0, Y is the 4-bit sum of A and B.
    check_add_mode_result: assert property (
        @($global_clock) (mode === 1'b0) |-> (Y == (A + B))
    );

    // In mode 1, the subtraction result is negated, so Y equals B minus A.
    check_mode1_result: assert property (
        @($global_clock) (mode === 1'b1) |-> (Y == (B - A))
    );

    // Non-0/1 mode values take the default branch and clear Y.
    check_default_mode_clears_y: assert property (
        @($global_clock) ((mode !== 1'b0) && (mode !== 1'b1)) |-> (Y == 4'b0000)
    );

    // Equal operands cancel to zero in mode 1.
    check_mode1_equal_operands_zero: assert property (
        @($global_clock) ((mode === 1'b1) && (A == B)) |-> (Y == 4'b0000)
    );

    // A zero left operand passes B through in add mode.
    check_add_mode_zero_a_passthrough_b: assert property (
        @($global_clock) ((mode === 1'b0) && (A == 4'b0000)) |-> (Y == B)
    );

    // A zero right operand passes A through in add mode.
    check_add_mode_zero_b_passthrough_a: assert property (
        @($global_clock) ((mode === 1'b0) && (B == 4'b0000)) |-> (Y == A)
    );

    // A zero left operand passes B through in mode 1 because Y = B - A.
    check_mode1_zero_a_returns_b: assert property (
        @($global_clock) ((mode === 1'b1) && (A == 4'b0000)) |-> (Y == B)
    );

    // A zero right operand in mode 1 makes Y the two's complement of A.
    check_mode1_zero_b_returns_neg_a: assert property (
        @($global_clock) ((mode === 1'b1) && (B == 4'b0000)) |-> (Y == (4'b0000 - A))
    );

endmodule