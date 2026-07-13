module comparator_4bit_sva (
    input logic [3:0] in_a,
    input logic [3:0] in_b,
    input logic clk,
    input logic eq,
    input logic gt,
    input logic lt
);

    // Posedge clk only; no reset; sequential comparator with registered inputs and outputs.

    // Equal sampled inputs produce only eq two cycles later.
    check_equal_case: assert property (
        @(posedge clk)
        (in_a == in_b) |-> ##2 (eq && !gt && !lt)
    );

    // Greater-than sampled inputs produce only gt two cycles later.
    check_greater_case: assert property (
        @(posedge clk)
        (in_a > in_b) |-> ##2 (!eq && gt && !lt)
    );

    // Less-than sampled inputs produce only lt two cycles later.
    check_less_case: assert property (
        @(posedge clk)
        (in_a < in_b) |-> ##2 (!eq && !gt && lt)
    );

    // After the pipeline delay, at least one result output is asserted.
    check_result_present: assert property (
        @(posedge clk)
        1'b1 |-> ##2 (eq || gt || lt)
    );

    // eq and gt are never asserted together after the pipeline delay.
    check_eq_gt_mutex: assert property (
        @(posedge clk)
        1'b1 |-> ##2 !(eq && gt)
    );

    // eq and lt are never asserted together after the pipeline delay.
    check_eq_lt_mutex: assert property (
        @(posedge clk)
        1'b1 |-> ##2 !(eq && lt)
    );

    // gt and lt are never asserted together after the pipeline delay.
    check_gt_lt_mutex: assert property (
        @(posedge clk)
        1'b1 |-> ##2 !(gt && lt)
    );

    // eq high reflects equal sampled inputs from two cycles earlier.
    check_eq_reflects_equal_inputs: assert property (
        @(posedge clk)
        1'b1 |-> ##2 (eq |-> ($past(in_a, 2) == $past(in_b, 2)))
    );

    // gt high reflects greater sampled inputs from two cycles earlier.
    check_gt_reflects_greater_inputs: assert property (
        @(posedge clk)
        1'b1 |-> ##2 (gt |-> ($past(in_a, 2) > $past(in_b, 2)))
    );

    // lt high reflects smaller sampled inputs from two cycles earlier.
    check_lt_reflects_less_inputs: assert property (
        @(posedge clk)
        1'b1 |-> ##2 (lt |-> ($past(in_a, 2) < $past(in_b, 2)))
    );

endmodule