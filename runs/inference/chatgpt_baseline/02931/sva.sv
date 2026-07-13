module comparator_sva (
    input logic CLK,
    input logic [3:0] a,
    input logic [3:0] b,
    input logic gt,
    input logic lt,
    input logic eq
);
    // Exactly one of gt/lt/eq must be HIGH for any a,b.
    outputs_onehot: assert property (
        @(posedge CLK) disable iff (1'b0) $onehot({gt, lt, eq})
    );

    // When a > b, outputs must be gt=1, lt=0, eq=0.
    a_gt_b_sets_outputs: assert property (
        @(posedge CLK) disable iff (1'b0) (a > b) |-> (gt && !lt && !eq)
    );

    // When a < b, outputs must be gt=0, lt=1, eq=0.
    a_lt_b_sets_outputs: assert property (
        @(posedge CLK) disable iff (1'b0) (a < b) |-> (!gt && lt && !eq)
    );

    // When a == b, outputs must be gt=0, lt=0, eq=1.
    a_eq_b_sets_outputs: assert property (
        @(posedge CLK) disable iff (1'b0) (a == b) |-> (!gt && !lt && eq)
    );

    // If gt is HIGH, then a > b.
    gt_means_a_gt_b: assert property (
        @(posedge CLK) disable iff (1'b0) gt |-> (a > b)
    );

    // If lt is HIGH, then a < b.
    lt_means_a_lt_b: assert property (
        @(posedge CLK) disable iff (1'b0) lt |-> (a < b)
    );

    // If eq is HIGH, then a == b.
    eq_means_a_eq_b: assert property (
        @(posedge CLK) disable iff (1'b0) eq |-> (a == b)
    );

    // When a >= b, lt must be LOW.
    no_lt_when_a_ge_b: assert property (
        @(posedge CLK) disable iff (1'b0) (a >= b) |-> (!lt)
    );

    // When a <= b, gt must be LOW.
    no_gt_when_a_le_b: assert property (
        @(posedge CLK) disable iff (1'b0) (a <= b) |-> (!gt)
    );

    // When a != b, eq must be LOW.
    no_eq_when_a_ne_b: assert property (
        @(posedge CLK) disable iff (1'b0) (a != b) |-> (!eq)
    );
endmodule