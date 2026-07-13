module Comparator_sva #(
  parameter int n = 8
) (
  input  logic [n-1:0] a,
  input  logic [n-1:0] b,
  input  logic         eq,
  input  logic         gt,
  input  logic         lt
);

    ///// Output coding /////
    // Exactly one of eq/gt/lt must be HIGH (one-hot).
    check_outputs_onehot: assert property (
        @(posedge a[0] or negedge a[0] or posedge b[0] or negedge b[0] or
          posedge eq   or negedge eq   or posedge gt   or negedge gt   or
          posedge lt   or negedge lt)
        $onehot({eq, gt, lt})
    );

    // Outputs are never X/Z.
    check_outputs_known: assert property (
        @(posedge a[0] or negedge a[0] or posedge b[0] or negedge b[0] or
          posedge eq   or negedge eq   or posedge gt   or negedge gt   or
          posedge lt   or negedge lt)
        !$isunknown({eq, gt, lt})
    );

    // Outputs are never all zero (completeness).
    check_outputs_nonzero: assert property (
        @(posedge a[0] or negedge a[0] or posedge b[0] or negedge b[0] or
          posedge eq   or negedge eq   or posedge gt   or negedge gt   or
          posedge lt   or negedge lt)
        (eq || gt || lt)
    );

    ///// Functional mapping /////
    // If a == b, then eq=1 and gt=0, lt=0.
    map_equal_to_eq: assert property (
        @(posedge a[0] or negedge a[0] or posedge b[0] or negedge b[0] or
          posedge eq   or negedge eq   or posedge gt   or negedge gt   or
          posedge lt   or negedge lt)
        (a == b) |-> (eq && !gt && !lt)
    );

    // If a > b, then gt=1 and eq=0, lt=0.
    map_greater_to_gt: assert property (
        @(posedge a[0] or negedge a[0] or posedge b[0] or negedge b[0] or
          posedge eq   or negedge eq   or posedge gt   or negedge gt   or
          posedge lt   or negedge lt)
        (a > b) |-> (gt && !eq && !lt)
    );

    // If neither (a == b) nor (a > b), then lt=1 and eq=0, gt=0.
    map_else_to_lt: assert property (
        @(posedge a[0] or negedge a[0] or posedge b[0] or negedge b[0] or
          posedge eq   or negedge eq   or posedge gt   or negedge gt   or
          posedge lt   or negedge lt)
        (!(a == b) && !(a > b)) |-> (lt && !eq && !gt)
    );

    ///// Output-to-input consistency /////
    // eq implies a == b.
    eq_implies_equal: assert property (
        @(posedge a[0] or negedge a[0] or posedge b[0] or negedge b[0] or
          posedge eq   or negedge eq   or posedge gt   or negedge gt   or
          posedge lt   or negedge lt)
        eq |-> (a == b)
    );

    // gt implies a > b.
    gt_implies_greater: assert property (
        @(posedge a[0] or negedge a[0] or posedge b[0] or negedge b[0] or
          posedge eq   or negedge eq   or posedge gt   or negedge gt   or
          posedge lt   or negedge lt)
        gt |-> (a > b)
    );

endmodule