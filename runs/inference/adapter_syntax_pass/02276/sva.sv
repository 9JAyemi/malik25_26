module mag_comparator_sva (
    input logic clk,
    input logic [1:0] A,
    input logic [1:0] B,
    input logic EQ,
    input logic GT,
    input logic LT
);

    // EQ must match the equality comparison of A and B.
    check_eq_definition: assert property (
        @(posedge clk) EQ == (A == B)
    );

    // GT must match the greater-than comparison of A and B.
    check_gt_definition: assert property (
        @(posedge clk) GT == (A > B)
    );

    // LT must match the less-than comparison of A and B.
    check_lt_definition: assert property (
        @(posedge clk) LT == (A < B)
    );

    // EQ and GT cannot be high together.
    check_eq_excludes_gt: assert property (
        @(posedge clk) !(EQ && GT)
    );

    // EQ and LT cannot be high together.
    check_eq_excludes_lt: assert property (
        @(posedge clk) !(EQ && LT)
    );

    // GT and LT cannot be high together.
    check_gt_excludes_lt: assert property (
        @(posedge clk) !(GT && LT)
    );

    // Exactly one of EQ, GT, or LT must be high.
    check_output_onehot: assert property (
        @(posedge clk) $onehot({EQ, GT, LT})
    );

endmodule