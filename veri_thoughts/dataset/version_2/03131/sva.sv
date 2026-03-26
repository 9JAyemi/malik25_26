module signed_mag_comparator_sva (
    input logic signed [3:0] A,
    input logic signed [3:0] B,
    input logic eq,
    input logic lt,
    input logic gt
);

    // eq matches the equality comparison.
    check_eq_definition: assert property (
        @($global_clock) (eq === (A == B))
    );

    // lt matches the signed less-than comparison.
    check_lt_definition: assert property (
        @($global_clock) (lt === (A < B))
    );

    // gt matches the signed greater-than comparison.
    check_gt_definition: assert property (
        @($global_clock) (gt === (A > B))
    );

    // eq excludes lt and gt.
    check_eq_exclusive: assert property (
        @($global_clock) (eq === 1'b1) |-> ((lt === 1'b0) && (gt === 1'b0))
    );

    // lt excludes eq and gt.
    check_lt_exclusive: assert property (
        @($global_clock) (lt === 1'b1) |-> ((eq === 1'b0) && (gt === 1'b0))
    );

    // gt excludes eq and lt.
    check_gt_exclusive: assert property (
        @($global_clock) (gt === 1'b1) |-> ((eq === 1'b0) && (lt === 1'b0))
    );

endmodule