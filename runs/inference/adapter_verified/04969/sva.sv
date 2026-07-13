module comparator_4bit_sva (
    input logic clk,
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

// Reset clears all outputs.
    check_reset_clears_outputs: assert property (
        @(posedge clk) reset |-> (EQ == 1'b0) && (GT == 1'b0) && (LT == 1'b0)
    );

// When disabled, all outputs are low.
    check_disabled_clears_outputs: assert property (
        @(posedge clk) disable iff (reset) (!enable) |-> (EQ == 1'b0) && (GT == 1'b0) && (LT == 1'b0)
    );

// EQ can only rise when A equals B and enable is high.
    check_eq_rise_condition: assert property (
        @(posedge clk) disable iff (reset) $rose(EQ) |-> (enable && (A == B))
    );

// GT can only rise when A is greater than B and enable is high.
    check_gt_rise_condition: assert property (
        @(posedge clk) disable iff (reset) $rose(GT) |-> (enable && (A > B))
    );

// LT can only rise when A is less than B and enable is high.
    check_lt_rise_condition: assert property (
        @(posedge clk) disable iff (reset) $rose(LT) |-> (enable && (A < B))
    );

// EQ, GT, and LT are never asserted together.
    check_outputs_mutex: assert property (
        @(posedge clk) disable iff (reset) !(EQ && GT && LT)
    );

// When enabled and A equals B, EQ is high and GT/LT are low.
    check_equal_case: assert property (
        @(posedge clk) disable iff (reset) (enable && (A == B)) |-> (EQ && !GT && !LT)
    );

// When enabled and A is greater than B, GT is high and EQ/LT are low.
    check_greater_case: assert property (
        @(posedge clk) disable iff (reset) (enable && (A > B)) |-> (GT && !EQ && !LT)
    );

// When enabled and A is less than B, LT is high and EQ/GT are low.
    check_less_case: assert property (
        @(posedge clk) disable iff (reset) (enable && (A < B)) |-> (LT && !EQ && !GT)
    );

endmodule
