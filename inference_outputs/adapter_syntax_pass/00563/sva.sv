module comparator_block_sva #(
    parameter int n = 8
)(
    input logic clk,
    input logic [n-1:0] a,
    input logic [n-1:0] b,
    input logic gt,
    input logic lt,
    input logic eq
);

    // eq must match the RTL's equality comparison.
    check_eq_definition: assert property (
        @(posedge clk) eq == (a == b)
    );

    // gt must match the RTL's greater-than comparison.
    check_gt_definition: assert property (
        @(posedge clk) gt == (a > b)
    );

    // lt must match the RTL's less-than comparison.
    check_lt_definition: assert property (
        @(posedge clk) lt == (a < b)
    );

    // eq must be the logical inverse of gt.
    check_eq_complements_gt: assert property (
        @(posedge clk) eq == !gt
    );

    // eq must be the logical inverse of lt.
    check_eq_complements_lt: assert property (
        @(posedge clk) eq == !lt
    );

    // gt and lt cannot be high together.
    check_gt_lt_mutex: assert property (
        @(posedge clk) !(gt && lt)
    );

    // When a and b are equal, only eq can be high.
    check_eq_only_when_equal: assert property (
        @(posedge clk) (a == b) |-> (eq && !gt && !lt)
    );

    // When a is greater than b, only gt can be high.
    check_gt_only_when_greater: assert property (
        @(posedge clk) (a > b) |-> (gt && !eq && !lt)
    );

    // When a is less than b, only lt can be high.
    check_lt_only_when_less: assert property (
        @(posedge clk) (a < b) |-> (lt && !eq && !gt)
    );

endmodule