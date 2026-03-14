module comparator_sva (
    input logic clk,
    input logic [7:0] in1,
    input logic [7:0] in2,
    input logic out_eq,
    input logic out_gt,
    input logic out_lt
);
    // Outputs exactly match the comparator functions of inputs.
    check_functional_mapping: assert property (
        @(posedge clk) (out_eq == (in1 == in2)) && (out_gt == (in1 > in2)) && (out_lt == (in1 < in2))
    );

    // Exactly one output is HIGH at any time (one-hot).
    check_outputs_onehot: assert property (
        @(posedge clk) $onehot({out_eq, out_gt, out_lt})
    );

    // Outputs are never all zero.
    check_outputs_not_all_zero: assert property (
        @(posedge clk) (out_eq || out_gt || out_lt)
    );

    // When inputs are equal, only out_eq is HIGH.
    check_eq_when_equal: assert property (
        @(posedge clk) (in1 == in2) |-> (out_eq && !out_gt && !out_lt)
    );

    // When in1 > in2, only out_gt is HIGH.
    check_gt_when_greater: assert property (
        @(posedge clk) (in1 > in2) |-> (!out_eq && out_gt && !out_lt)
    );

    // When in1 < in2, only out_lt is HIGH.
    check_lt_when_less: assert property (
        @(posedge clk) (in1 < in2) |-> (!out_eq && !out_gt && out_lt)
    );

    // If out_eq is HIGH, inputs must be equal.
    check_eq_implies_equal: assert property (
        @(posedge clk) out_eq |-> (in1 == in2)
    );

    // If out_gt is HIGH, in1 must be greater than in2.
    check_gt_implies_greater: assert property (
        @(posedge clk) out_gt |-> (in1 > in2)
    );

    // If out_lt is HIGH, in1 must be less than in2.
    check_lt_implies_less: assert property (
        @(posedge clk) out_lt |-> (in1 < in2)
    );

    // No two outputs can be HIGH simultaneously (mutual exclusion).
    check_mutex_pairs: assert property (
        @(posedge clk) !(out_eq && out_gt) && !(out_eq && out_lt) && !(out_gt && out_lt)
    );
endmodule