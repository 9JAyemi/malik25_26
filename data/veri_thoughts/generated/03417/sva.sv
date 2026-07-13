module top_module_sva (
    input logic clk,
    input logic signed [3:0] A,
    input logic signed [3:0] B,
    input logic EN,
    input logic [15:0] Q,
    input logic C,
    input logic [3:0] abs_A,
    input logic [3:0] abs_B,
    input logic eq,
    input logic gt,
    input logic lt,
    input logic [1:0] sel
);

    // C directly reflects the comparator equality result.
    check_c_matches_eq: assert property (
        @(posedge clk) (C == eq)
    );

    // eq is high exactly when A and B are equal.
    check_eq_definition: assert property (
        @(posedge clk) (eq == (A == B))
    );

    // gt is high exactly when A is greater than B.
    check_gt_definition: assert property (
        @(posedge clk) (gt == (A > B))
    );

    // lt is high exactly when A is less than B.
    check_lt_definition: assert property (
        @(posedge clk) (lt == (A < B))
    );

    // Exactly one compare result is true for any pair of signed inputs.
    check_compare_partition: assert property (
        @(posedge clk)
        ((eq && !gt && !lt) ||
         (!eq && gt && !lt) ||
         (!eq && !gt && lt))
    );

    // abs_A matches the implemented two's-complement absolute value.
    check_abs_a_definition: assert property (
        @(posedge clk) (abs_A == ((A < 4'sd0) ? (~A + 4'b0001) : A))
    );

    // abs_B matches the implemented two's-complement absolute value.
    check_abs_b_definition: assert property (
        @(posedge clk) (abs_B == ((B < 4'sd0) ? (~B + 4'b0001) : B))
    );

    // sel goes to 2'b11 whenever EN is low.
    check_sel_when_disabled: assert property (
        @(posedge clk) (!EN) |-> (sel == 2'b11)
    );

    // Equal inputs select decoder input 2'b00 when enabled.
    check_sel_for_equal_case: assert property (
        @(posedge clk) (EN && eq) |-> (sel == 2'b00)
    );

    // Greater-than selects decoder input 2'b01 when enabled.
    check_sel_for_greater_case: assert property (
        @(posedge clk) (EN && gt) |-> (sel == 2'b01)
    );

    // Less-than selects decoder input 2'b10 when enabled.
    check_sel_for_less_case: assert property (
        @(posedge clk) (EN && lt) |-> (sel == 2'b10)
    );

    // Q is zero whenever the decoder is disabled.
    check_q_zero_when_disabled: assert property (
        @(posedge clk) (!EN) |-> (Q == 16'h0000)
    );

    // Equal signed inputs drive C high and Q bit 0 when enabled.
    check_outputs_for_equal_inputs: assert property (
        @(posedge clk) (EN && (A == B)) |-> (C && (Q == 16'h0001))
    );

    // A greater than B drives Q bit 1 and clears C when enabled.
    check_outputs_for_greater_inputs: assert property (
        @(posedge clk) (EN && (A > B)) |-> ((!C) && (Q == 16'h0002))
    );

    // A less than B drives Q bit 2 and clears C when enabled.
    check_outputs_for_less_inputs: assert property (
        @(posedge clk) (EN && (A < B)) |-> ((!C) && (Q == 16'h0004))
    );

    // The top-level Q output only reaches the implemented values.
    check_q_legal_values: assert property (
        @(posedge clk)
        ((Q == 16'h0000) ||
         (Q == 16'h0001) ||
         (Q == 16'h0002) ||
         (Q == 16'h0004))
    );

endmodule