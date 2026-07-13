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

    // Reset forces all outputs low.
    check_reset_clears_outputs: assert property (
        @(posedge reset) reset |-> (EQ == 1'b0 && GT == 1'b0 && LT == 1'b0)
    );

    // When disabled, all outputs are low.
    check_disable_clears_outputs: assert property (
        @(posedge enable) !enable |-> (EQ == 1'b0 && GT == 1'b0 && LT == 1'b0)
    );

    // When enabled without loads, outputs remain unchanged.
    check_hold_when_enabled_without_loads: assert property (
        @(posedge enable) enable && !load_A && !load_B |-> $stable({EQ, GT, LT})
    );

    // Equal data makes EQ high and GT/LT low.
    check_equal_sets_eq: assert property (
        @(posedge enable) enable && (A == B) |-> (EQ == 1'b1 && GT == 1'b0 && LT == 1'b0)
    );

    // Greater data makes GT high and EQ/LT low.
    check_greater_sets_gt: assert property (
        @(posedge enable) enable && (A > B) |-> (EQ == 1'b0 && GT == 1'b1 && LT == 1'b0)
    );

    // Less data makes LT high and EQ/GT low.
    check_less_sets_lt: assert property (
        @(posedge enable) enable && (A < B) |-> (EQ == 1'b0 && GT == 1'b0 && LT == 1'b1)
    );

    // EQ and GT are never asserted together.
    check_eq_gt_mutex: assert property (
        @(posedge enable) !(EQ && GT)
    );

    // EQ and LT are never asserted together.
    check_eq_lt_mutex: assert property (
        @(posedge enable) !(EQ && LT)
    );

    // GT and LT are never asserted together.
    check_gt_lt_mutex: assert property (
        @(posedge enable) !(GT && LT)
    );

    // At least one comparison result is asserted.
    check_one_result_asserted: assert property (
        @(posedge enable) (EQ || GT || LT)
    );

endmodule