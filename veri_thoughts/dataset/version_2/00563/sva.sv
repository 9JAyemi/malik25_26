module comparator_block_sva #(
    parameter n = 8
)(
    input logic clk,
    input logic [n-1:0] a,
    input logic [n-1:0] b,
    input logic gt,
    input logic lt,
    input logic eq
);

    // gt matches the OR of zero-extended bit positions where a is 1 and b is 0.
    check_gt_definition: assert property (
        @(posedge clk) gt == (|(({1'b0, a}) & ~({1'b0, b})))
    );

    // lt matches the OR of zero-extended bit positions where a is 0 and b is 1.
    check_lt_definition: assert property (
        @(posedge clk) lt == (|(~({1'b0, a}) & ({1'b0, b})))
    );

    // eq matches the AND of zero-extended bitwise equality results.
    check_eq_definition: assert property (
        @(posedge clk) eq == (&((({1'b0, a}) ~^ ({1'b0, b}))))
    );

    // Equal inputs must drive eq high and both difference flags low.
    check_equal_inputs_outputs: assert property (
        @(posedge clk) (a == b) |-> (eq && !gt && !lt)
    );

    // Different inputs must clear eq and assert at least one difference flag.
    check_different_inputs_outputs: assert property (
        @(posedge clk) (a != b) |-> (!eq && (gt || lt))
    );

    // eq is asserted exactly when neither gt nor lt is asserted.
    check_eq_matches_no_gt_lt: assert property (
        @(posedge clk) eq == !(gt || lt)
    );

    // gt can only be high when a and b differ.
    check_gt_indicates_difference: assert property (
        @(posedge clk) gt |-> (a != b)
    );

    // lt can only be high when a and b differ.
    check_lt_indicates_difference: assert property (
        @(posedge clk) lt |-> (a != b)
    );

    // Stable inputs keep the combinational outputs stable.
    check_stable_inputs_stable_outputs: assert property (
        @(posedge clk) ($stable(a) && $stable(b)) |-> $stable({gt, lt, eq})
    );

endmodule