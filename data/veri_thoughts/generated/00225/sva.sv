module top_module_sva (
    input logic clk,
    input logic signed [3:0] A,
    input logic signed [3:0] B,
    input logic signed [3:0] out,
    input logic eq,
    input logic gt,
    input logic lt,
    input logic overflow
);

    // eq must reflect signed equality.
    check_eq_relation: assert property (
        @(posedge clk) (eq == (A == B))
    );

    // gt must reflect signed greater-than.
    check_gt_relation: assert property (
        @(posedge clk) (gt == (A > B))
    );

    // lt must reflect signed less-than.
    check_lt_relation: assert property (
        @(posedge clk) (lt == (A < B))
    );

    // Exactly one comparator result must be asserted.
    check_compare_onehot: assert property (
        @(posedge clk) (eq || gt || lt) && !(eq && gt) && !(eq && lt) && !(gt && lt)
    );

    // overflow must match 4-bit signed addition overflow.
    check_overflow_relation: assert property (
        @(posedge clk) (overflow == ((A[3] == B[3]) && ((A + B)[3] != A[3])))
    );

    // out must follow the top-level mux selection.
    check_out_mux_relation: assert property (
        @(posedge clk) (out == (eq ? (A + B) : (gt ? A : B)))
    );

    // When A equals B, out must be the wrapped 4-bit sum.
    check_out_when_equal: assert property (
        @(posedge clk) eq |-> (out == (A + B))
    );

    // When A is greater than B, out must pass through A.
    check_out_when_greater: assert property (
        @(posedge clk) gt |-> (out == A)
    );

    // When A is less than B, out must pass through B.
    check_out_when_less: assert property (
        @(posedge clk) lt |-> (out == B)
    );

endmodule