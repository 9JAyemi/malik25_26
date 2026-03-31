module mag_comparator_sva (
    input logic clk,
    input logic [1:0] A,
    input logic [1:0] B,
    input logic EQ,
    input logic GT,
    input logic LT
);

// EQ must match the equality comparison of A and B.
    check_eq_definition: assert property (
        @(posedge clk) EQ == (A == B)
    );

// GT must match the greater-than comparison of A and B.
    check_gt_definition: assert property (
        @(posedge clk) GT == (A > B)
    );

// LT must match the less-than comparison of A and B.
    check_lt_definition: assert property (
        @(posedge clk) LT == (A < B)
    );

// Exactly one of EQ, GT, or LT must be HIGH.
    check_outputs_onehot: assert property (
        @(posedge clk) $onehot({EQ, GT, LT})
    );

// When A equals B, only EQ can be HIGH.
    check_eq_when_equal: assert property (
        @(posedge clk) (A == B) |-> (EQ && !GT && !LT)
    );

// When A is greater than B, only GT can be HIGH.
    check_gt_when_greater: assert property (
        @(posedge clk) (A > B) |-> (GT && !EQ && !LT)
    );

// When A is less than B, only LT can be HIGH.
    check_lt_when_less: assert property (
        @(posedge clk) (A < B) |-> (LT && !EQ && !GT)
    );

endmodule
