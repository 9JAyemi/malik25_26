module four_bit_comparator_sva (
    input logic clk,
    input logic [3:0] a,
    input logic [3:0] b,
    input logic eq,
    input logic gt,
    input logic lt
);
    // eq must equal (a == b)
    check_eq_definition: assert property (
        @(posedge clk) (eq == (a == b))
    );

    // gt must equal (a > b)
    check_gt_definition: assert property (
        @(posedge clk) (gt == (a > b))
    );

    // lt must equal (a < b)
    check_lt_definition: assert property (
        @(posedge clk) (lt == (a < b))
    );

    // Exactly one of {eq, gt, lt} is HIGH
    check_onehot_relation: assert property (
        @(posedge clk) ((eq + gt + lt) == 1)
    );

    // If eq is HIGH, gt and lt must be LOW
    check_eq_exclusive: assert property (
        @(posedge clk) eq |-> (!gt && !lt)
    );

    // If gt is HIGH, eq and lt must be LOW
    check_gt_exclusive: assert property (
        @(posedge clk) gt |-> (!eq && !lt)
    );

    // If lt is HIGH, eq and gt must be LOW
    check_lt_exclusive: assert property (
        @(posedge clk) lt |-> (!eq && !gt)
    );

    // If a equals b, outputs must be eq=1, gt=0, lt=0
    check_outputs_when_equal: assert property (
        @(posedge clk) (a == b) |-> (eq && !gt && !lt)
    );

    // If a is greater than b, outputs must be gt=1, eq=0, lt=0
    check_outputs_when_greater: assert property (
        @(posedge clk) (a > b) |-> (gt && !eq && !lt)
    );

    // If a is less than b, outputs must be lt=1, eq=0, gt=0
    check_outputs_when_less: assert property (
        @(posedge clk) (a < b) |-> (lt && !eq && !gt)
    );
endmodule