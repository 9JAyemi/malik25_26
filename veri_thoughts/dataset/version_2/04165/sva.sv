module comparator_4bit_sva (
    input logic       clk,
    input logic [3:0] in1,
    input logic [3:0] in2,
    input logic       eq,
    input logic       gt,
    input logic       lt
);

    // eq matches the equality comparison.
    check_eq_matches_inputs: assert property (
        @(posedge clk) (eq === (in1 == in2))
    );

    // gt matches the greater-than comparison.
    check_gt_matches_inputs: assert property (
        @(posedge clk) (gt === (in1 > in2))
    );

    // lt matches the less-than comparison.
    check_lt_matches_inputs: assert property (
        @(posedge clk) (lt === (in1 < in2))
    );

    // Comparison outputs never assert together.
    check_outputs_mutually_exclusive: assert property (
        @(posedge clk) (!(eq && gt) && !(eq && lt) && !(gt && lt))
    );

    // One comparison result is always indicated.
    check_outputs_complete: assert property (
        @(posedge clk) (eq || gt || lt)
    );

    // Equal inputs drive only eq high.
    check_equal_case_result: assert property (
        @(posedge clk) ((in1 == in2) |-> (eq && !gt && !lt))
    );

    // Larger in1 drives only gt high.
    check_greater_case_result: assert property (
        @(posedge clk) ((in1 > in2) |-> (!eq && gt && !lt))
    );

    // Smaller in1 drives only lt high.
    check_less_case_result: assert property (
        @(posedge clk) ((in1 < in2) |-> (!eq && !gt && lt))
    );

endmodule