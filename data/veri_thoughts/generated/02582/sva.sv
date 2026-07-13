module comparator_sva (
    input logic clk,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic EQ,
    input logic GT,
    input logic LT,
    input logic NE
);
    // EQ reflects A == B.
    check_eq_definition: assert property (
        @(posedge clk) (EQ == (A == B))
    );

    // GT reflects A > B.
    check_gt_definition: assert property (
        @(posedge clk) (GT == (A > B))
    );

    // LT reflects A < B.
    check_lt_definition: assert property (
        @(posedge clk) (LT == (A < B))
    );

    // NE reflects A != B.
    check_ne_definition: assert property (
        @(posedge clk) (NE == (A != B))
    );

    // Exactly one of EQ, GT, LT is HIGH at any time.
    check_egtlt_onehot: assert property (
        @(posedge clk) $onehot({EQ, GT, LT})
    );

    // NE is the logical complement of EQ.
    check_ne_complement_eq: assert property (
        @(posedge clk) (NE == !EQ)
    );

    // NE equals (GT or LT).
    check_ne_eq_gt_or_lt: assert property (
        @(posedge clk) (NE == (GT || LT))
    );

    // If GT is HIGH, LT must be LOW in the same cycle.
    check_gt_excludes_lt: assert property (
        @(posedge clk) GT |-> !LT
    );

    // If LT is HIGH, GT must be LOW in the same cycle.
    check_lt_excludes_gt: assert property (
        @(posedge clk) LT |-> !GT
    );

    // If EQ is HIGH, both GT and LT must be LOW.
    check_eq_excludes_gt_lt: assert property (
        @(posedge clk) EQ |-> (!GT && !LT)
    );
endmodule