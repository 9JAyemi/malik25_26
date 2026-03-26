module comparator_sva (
    input logic clk,
    input logic [3:0] a,
    input logic [3:0] b,
    input logic equal,
    input logic greater,
    input logic less
);

    // When inputs are equal, only equal is asserted.
    check_equal_case: assert property (
        @(posedge clk) (a == b) |-> (equal && !greater && !less)
    );

    // When a is greater than b, only greater is asserted.
    check_greater_case: assert property (
        @(posedge clk) (a > b) |-> (!equal && greater && !less)
    );

    // When a is less than b, only less is asserted.
    check_less_case: assert property (
        @(posedge clk) (a < b) |-> (!equal && !greater && less)
    );

    // equal high means the inputs must match.
    check_equal_implies_inputs_equal: assert property (
        @(posedge clk) equal |-> (a == b)
    );

    // greater high means a must be larger than b.
    check_greater_implies_a_gt_b: assert property (
        @(posedge clk) greater |-> (a > b)
    );

    // less high means a must be smaller than b.
    check_less_implies_a_lt_b: assert property (
        @(posedge clk) less |-> (a < b)
    );

    // Exactly one comparison result is asserted at a time.
    check_outputs_onehot: assert property (
        @(posedge clk)
        (equal || greater || less) &&
        !(equal && greater) &&
        !(equal && less) &&
        !(greater && less)
    );

endmodule