module barrel_shifter_sva (
    input logic [3:0] A,
    input logic [3:0] B,
    input logic [3:0] result,
    input logic [3:0] stage1_out,
    input logic [3:0] stage2_out,
    input logic [3:0] abs_B
);

    // No RTL clock or reset; sample combinational behavior on $global_clock.

    // abs_B matches B when B selects the left-shift path.
    check_abs_b_positive_case: assert property (
        @($global_clock) (B[3] == 1'b0) |-> (abs_B == B)
    );

    // abs_B is the two's-complement magnitude when B selects the right-shift path.
    check_abs_b_negative_case: assert property (
        @($global_clock) (B[3] == 1'b1) |-> (abs_B == (~B + 1'b1))
    );

    // stage1_out performs the left shift for non-negative B.
    check_stage1_left_shift: assert property (
        @($global_clock) (B[3] == 1'b0) |-> (stage1_out == (A << B))
    );

    // stage1_out performs the right shift by abs_B for negative B.
    check_stage1_right_shift: assert property (
        @($global_clock) (B[3] == 1'b1) |-> (stage1_out == (A >> abs_B))
    );

    // stage2_out is a direct copy of stage1_out.
    check_stage2_copies_stage1: assert property (
        @($global_clock) (stage2_out == stage1_out)
    );

    // result is a direct copy of stage2_out.
    check_result_copies_stage2: assert property (
        @($global_clock) (result == stage2_out)
    );

    // result matches the left shift path for non-negative B.
    check_result_left_shift: assert property (
        @($global_clock) (B[3] == 1'b0) |-> (result == (A << B))
    );

    // result matches the right shift path for negative B.
    check_result_right_shift: assert property (
        @($global_clock) (B[3] == 1'b1) |-> (result == (A >> abs_B))
    );

endmodule