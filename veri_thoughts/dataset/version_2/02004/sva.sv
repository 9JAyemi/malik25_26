module binary_comparator_sva (
    input logic clk,          // verification clock for sampling assertions
    input logic [7:0] A,
    input logic [7:0] B,
    input logic EQ,
    input logic LT,
    input logic GT
);
    // DUT has no reset; purely combinational logic sampled on clk.
    // Behavior: EQ=1 when A==B; LT=1 when A<B; GT=1 when A>B; exactly one high.

    // Exactly one of EQ/LT/GT is HIGH at any time.
    check_onehot_outputs: assert property (
        @(posedge clk) $onehot({EQ, LT, GT})
    );

    // When A equals B, EQ must be 1 and LT/GT must be 0.
    check_eq_when_equal: assert property (
        @(posedge clk) (A == B) |-> (EQ && !LT && !GT)
    );

    // If EQ is 1, then A must equal B.
    check_equal_implied_by_EQ: assert property (
        @(posedge clk) EQ |-> (A == B)
    );

    // When A is less than B, LT must be 1 and EQ/GT must be 0.
    check_lt_when_less: assert property (
        @(posedge clk) (A < B) |-> (!EQ && LT && !GT)
    );

    // If LT is 1, then A must be less than B.
    check_less_implied_by_LT: assert property (
        @(posedge clk) LT |-> (A < B)
    );

    // When A is greater than B, GT must be 1 and EQ/LT must be 0.
    check_gt_when_greater: assert property (
        @(posedge clk) (A > B) |-> (!EQ && !LT && GT)
    );

    // If GT is 1, then A must be greater than B.
    check_greater_implied_by_GT: assert property (
        @(posedge clk) GT |-> (A > B)
    );

endmodule