module comparator_sva (
    input logic clk,          // sampling clock for SVA (DUT has no clock/reset)
    input logic [2:0] a,
    input logic [2:0] b,
    input logic gt,
    input logic eq,
    input logic lt
);

    // Exactly one of gt/eq/lt is HIGH.
    check_outputs_onehot: assert property (
        @(posedge clk) $onehot({gt, eq, lt})
    );

    // If a > b then gt=1, eq=0, lt=0.
    check_outputs_when_a_gt_b: assert property (
        @(posedge clk) (a > b) |-> (gt && !eq && !lt)
    );

    // If a == b then eq=1, gt=0, lt=0.
    check_outputs_when_a_eq_b: assert property (
        @(posedge clk) (a == b) |-> (!gt && eq && !lt)
    );

    // If a < b then lt=1, gt=0, eq=0.
    check_outputs_when_a_lt_b: assert property (
        @(posedge clk) (a < b) |-> (!gt && !eq && lt)
    );

    // gt implies a > b.
    check_gt_implies_relation: assert property (
        @(posedge clk) gt |-> (a > b)
    );

    // eq implies a == b.
    check_eq_implies_relation: assert property (
        @(posedge clk) eq |-> (a == b)
    );

    // lt implies a < b.
    check_lt_implies_relation: assert property (
        @(posedge clk) lt |-> (a < b)
    );

endmodule