module mag_comparator_sva #(
    parameter n = 4
)(
    input logic clk,
    input logic [n-1:0] A,
    input logic [n-1:0] B,
    input logic GT,
    input logic EQ,
    input logic LT
);

    // GT matches the greater-than comparison.
    check_gt_matches_relation: assert property (
        @(posedge clk) (GT == (A > B))
    );

    // EQ matches the equality comparison.
    check_eq_matches_relation: assert property (
        @(posedge clk) (EQ == (A == B))
    );

    // LT matches the less-than comparison.
    check_lt_matches_relation: assert property (
        @(posedge clk) (LT == (A < B))
    );

    // GT and EQ are never asserted together.
    check_gt_eq_mutex: assert property (
        @(posedge clk) !(GT && EQ)
    );

    // GT and LT are never asserted together.
    check_gt_lt_mutex: assert property (
        @(posedge clk) !(GT && LT)
    );

    // EQ and LT are never asserted together.
    check_eq_lt_mutex: assert property (
        @(posedge clk) !(EQ && LT)
    );

    // At least one comparison result is asserted.
    check_result_present: assert property (
        @(posedge clk) (GT || EQ || LT)
    );

endmodule