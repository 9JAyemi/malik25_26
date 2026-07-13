module comparator_4bit_sva (
    input logic [3:0] A,
    input logic [3:0] B,
    input logic reset,
    input logic enable,
    input logic load_A,
    input logic load_B,
    input logic EQ,
    input logic GT,
    input logic LT
);

    // Reset clears all outputs and internal registers.
    check_reset_clears_outputs: assert property (
        @($global_clock)
        reset |-> ((EQ == 1'b0) && (GT == 1'b0) && (LT == 1'b0))
    );

    // Reset clears all outputs and internal registers.
    check_reset_clears_internal_state: assert property (
        @($global_clock)
        reset |-> ((A == 4'b0000) && (B == 4'b0000))
    );

    // When disabled, all outputs are low.
    check_disable_clears_outputs: assert property (
        @($global_clock) disable iff (reset)
        !enable |-> ((EQ == 1'b0) && (GT == 1'b0) && (LT == 1'b0))
    );

    // EQ is high only when A equals B.
    check_eq_definition: assert property (
        @($global_clock) disable iff (reset)
        (EQ == (A == B))
    );

    // GT is high only when A is greater than B.
    check_gt_definition: assert property (
        @($global_clock) disable iff (reset)
        (GT == (A > B))
    );

    // LT is high only when A is less than B.
    check_lt_definition: assert property (
        @($global_clock) disable iff (reset)
        (LT == (A < B))
    );

    // EQ and GT are never asserted together.
    check_eq_gt_mutex: assert property (
        @($global_clock) disable iff (reset)
        !(EQ && GT)
    );

    // EQ and LT are never asserted together.
    check_eq_lt_mutex: assert property (
        @($global_clock) disable iff (reset)
        !(EQ && LT)
    );

    // GT and LT are never asserted together.
    check_gt_lt_mutex: assert property (
        @($global_clock) disable iff (reset)
        !(GT && LT)
    );

    // EQ is high exactly when GT and LT are low.
    check_eq_excludes_others: assert property (
        @($global_clock) disable iff (reset)
        (EQ == ((!GT) && (!LT)))
    );

endmodule