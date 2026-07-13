module binary_adder_sva (
    input logic [3:0] A,
    input logic [3:0] B,
    input logic       CTRL,
    input logic [3:0] C
);

    // No RTL clock or reset; sample this combinational logic on the formal global clock.

    // In pass-through mode, C must equal the 4-bit sum of A and B.
    check_pass_through_mode_sum: assert property (
        @($global_clock) (CTRL == 1'b0) |-> (C == (A + B))
    );

    // In shift-and-add mode, C must equal the 4-bit sum of A[3:1] and B[3:1].
    check_shift_and_add_mode_sum: assert property (
        @($global_clock) (CTRL == 1'b1) |-> (C == ({1'b0, A[3:1]} + {1'b0, B[3:1]}))
    );

    // In shift-and-add mode, the least-significant bit of C must be zero.
    check_shift_and_add_mode_lsb_zero: assert property (
        @($global_clock) (CTRL == 1'b1) |-> (C[0] == 1'b0)
    );

    // In pass-through mode, adding zero on B must pass A through unchanged.
    check_pass_through_mode_zero_b_passthrough: assert property (
        @($global_clock) ((CTRL == 1'b0) && (B == 4'h0)) |-> (C == A)
    );

    // In pass-through mode, adding zero on A must pass B through unchanged.
    check_pass_through_mode_zero_a_passthrough: assert property (
        @($global_clock) ((CTRL == 1'b0) && (A == 4'h0)) |-> (C == B)
    );

    // In shift-and-add mode, zero on either operand must produce zero.
    check_shift_and_add_mode_zero_operand_zero: assert property (
        @($global_clock) ((CTRL == 1'b1) && ((A[3:1] == 3'h0) || (B[3:1] == 3'h0))) |-> (C == 4'h0)
    );

    // In pass-through mode, equal operands must double without carry-out.
    check_pass_through_mode_equal_operands_double: assert property (
        @($global_clock) ((CTRL == 1'b0) && (A == B)) |-> (C == ({1'b0, A} + {1'b0, A}))
    );

    // In shift-and-add mode, equal non-zero operands must double without carry-out.
    check_shift_and_add_mode_equal_nonzero_operands_double: assert property (
        @($global_clock) ((CTRL == 1'b1) && (A[3:1] == B[3:1]) && (A[3:1] != 3'h0)) |-> (C == ({1'b0, A[3:1]} + {1'b0, A[3:1]}))
    );

endmodule