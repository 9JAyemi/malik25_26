module top_module_sva (
    input logic clk,
    input logic [3:0] in0,
    input logic [3:0] in1,
    input logic DIR,
    input logic [1:0] AMT,
    input logic eq,
    input logic gt,
    input logic lt,
    input logic [3:0] out
);

    // RTL has no native clock or reset.
    // clk is only used to sample combinational behavior.

    // out must equal the barrel-shifted version of in0.
    check_out_matches_shift: assert property (
        @(posedge clk) out == (DIR ? (in0 >> AMT) : (in0 << AMT))
    );

    // A zero shift amount must pass in0 through unchanged.
    check_zero_shift_passthrough: assert property (
        @(posedge clk) (AMT == 2'b00) |-> (out == in0)
    );

    // DIR high selects a right shift.
    check_right_shift_behavior: assert property (
        @(posedge clk) DIR |-> (out == (in0 >> AMT))
    );

    // DIR low selects a left shift.
    check_left_shift_behavior: assert property (
        @(posedge clk) !DIR |-> (out == (in0 << AMT))
    );

    // eq must indicate equality between out and in1.
    check_eq_definition: assert property (
        @(posedge clk) eq == (out == in1)
    );

    // gt must indicate out is greater than in1.
    check_gt_definition: assert property (
        @(posedge clk) gt == (out > in1)
    );

    // lt must indicate out is less than in1.
    check_lt_definition: assert property (
        @(posedge clk) lt == (out < in1)
    );

    // eq cannot be high with gt or lt.
    check_eq_exclusive: assert property (
        @(posedge clk) !(eq && gt) && !(eq && lt)
    );

    // gt and lt cannot be high at the same time.
    check_gt_lt_mutex: assert property (
        @(posedge clk) !(gt && lt)
    );

    // The comparator must always report one relation.
    check_compare_complete: assert property (
        @(posedge clk) eq || gt || lt
    );

endmodule