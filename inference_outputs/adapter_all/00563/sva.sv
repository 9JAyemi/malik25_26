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

    // gt must reflect whether a is greater than b.
    check_gt_definition: assert property (
        @(posedge clk) gt == (a > b)
    );

    // lt must reflect whether a is less than b.
    check_lt_definition: assert property (
        @(posedge clk) lt == (a < b)
    );

    // eq must reflect whether a equals b.
    check_eq_definition: assert property (
        @(posedge clk) eq == (a == b)
    );

    // gt and lt cannot be high at the same time.
    check_gt_lt_mutex: assert property (
        @(posedge clk) !(gt && lt)
    );

    // When a equals b, both eq and gt must be low.
    check_eq_excludes_gt: assert property (
        @(posedge clk) (a == b) |-> (!eq && !gt)
    );

    // When a is greater than b, both gt and eq must be low.
    check_gt_excludes_eq: assert property (
        @(posedge clk) (a > b) |-> (gt && !eq)
    );

    // When a is less than b, both lt and eq must be low.
    check_lt_excludes_eq: assert property (
        @(posedge clk) (a < b) |-> (lt && !eq)
    );

    // If a and b are stable, the comparator outputs must remain stable.
    check_stable_when_inputs_stable: assert property (
        @(posedge clk) $stable({a, b}) |-> $stable({gt, lt, eq})
    );

endmodule