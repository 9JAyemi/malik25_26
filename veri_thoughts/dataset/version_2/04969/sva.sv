module comparator_4bit_sva (
    input logic [3:0] A,
    input logic [3:0] B,
    input logic reset,
    input logic enable,
    input logic load_A,
    input logic load_B,
    input logic EQ,
    input logic GT,
    input logic LT,
    input logic [3:0] A_reg,
    input logic [3:0] B_reg
);

    // No explicit RTL clock; sample assertions on the global clock.

    // Reset clears the internal latches and outputs.
    check_reset_clears_state: assert property (
        @($global_clock)
        reset |-> (A_reg == 4'b0000) && (B_reg == 4'b0000) &&
                  (EQ == 1'b0) && (GT == 1'b0) && (LT == 1'b0)
    );

    // When disabled, all compare outputs must be low.
    check_disable_clears_outputs: assert property (
        @($global_clock) disable iff (reset)
        !enable |-> (EQ == 1'b0) && (GT == 1'b0) && (LT == 1'b0)
    );

    // Loading A while enabled makes A_reg follow A.
    check_load_a_updates_a_reg: assert property (
        @($global_clock) disable iff (reset)
        enable && load_A |-> (A_reg == A)
    );

    // Loading B while enabled makes B_reg follow B.
    check_load_b_updates_b_reg: assert property (
        @($global_clock) disable iff (reset)
        enable && load_B |-> (B_reg == B)
    );

    // Equal latched operands drive only EQ high.
    check_equal_compare_outputs: assert property (
        @($global_clock) disable iff (reset)
        enable && (A_reg == B_reg) |-> (EQ == 1'b1) && (GT == 1'b0) && (LT == 1'b0)
    );

    // Greater-than latched operands drive only GT high.
    check_greater_compare_outputs: assert property (
        @($global_clock) disable iff (reset)
        enable && (A_reg > B_reg) |-> (EQ == 1'b0) && (GT == 1'b1) && (LT == 1'b0)
    );

    // Less-than latched operands drive only LT high.
    check_less_compare_outputs: assert property (
        @($global_clock) disable iff (reset)
        enable && (A_reg < B_reg) |-> (EQ == 1'b0) && (GT == 1'b0) && (LT == 1'b1)
    );

    // When enabled, exactly one compare output must be high.
    check_enabled_outputs_are_onehot: assert property (
        @($global_clock) disable iff (reset)
        enable |-> (EQ || GT || LT) &&
                   !(EQ && GT) &&
                   !(EQ && LT) &&
                   !(GT && LT)
    );

    // EQ high implies the latched operands are equal.
    check_eq_implies_equal_state: assert property (
        @($global_clock) disable iff (reset)
        EQ |-> enable && (A_reg == B_reg)
    );

    // GT high implies the latched A value is greater than latched B.
    check_gt_implies_greater_state: assert property (
        @($global_clock) disable iff (reset)
        GT |-> enable && (A_reg > B_reg)
    );

    // LT high implies the latched A value is less than latched B.
    check_lt_implies_less_state: assert property (
        @($global_clock) disable iff (reset)
        LT |-> enable && (A_reg < B_reg)
    );

endmodule