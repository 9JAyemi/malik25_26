module comparator_4bit_sva (
    input logic clk,
    input logic rst_n,
    input logic [3:0] in_a,
    input logic [3:0] in_b,
    input logic eq,
    input logic gt,
    input logic lt
);
    // eq reflects in_a == in_b.
    check_eq_definition: assert property (
        @(posedge clk) disable iff (!rst_n) eq == (in_a == in_b)
    );

    // gt reflects in_a > in_b.
    check_gt_definition: assert property (
        @(posedge clk) disable iff (!rst_n) gt == (in_a > in_b)
    );

    // lt reflects in_a < in_b.
    check_lt_definition: assert property (
        @(posedge clk) disable iff (!rst_n) lt == (in_a < in_b)
    );

    // Exactly one of eq/gt/lt is HIGH.
    check_outputs_onehot: assert property (
        @(posedge clk) disable iff (!rst_n) $onehot({eq, gt, lt})
    );

    // When not equal, gt and lt are complementary.
    check_eq_low_implies_gt_xor_lt: assert property (
        @(posedge clk) disable iff (!rst_n) (!eq) |-> (gt ^ lt)
    );

    // If eq is HIGH, gt and lt must be LOW.
    check_eq_excludes_gt_lt: assert property (
        @(posedge clk) disable iff (!rst_n) eq |-> (!gt && !lt)
    );
endmodule