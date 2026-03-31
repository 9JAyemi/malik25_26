module comparator_block_sva (
    input logic clk,
    input logic [7:0] a,
    input logic [7:0] b,
    input logic gt,
    input logic lt,
    input logic eq
);

// gt must equal the MSB of the signed comparison.
    check_gt_definition: assert property (
        @(posedge clk) gt == (a[7] & ~b[7])
    );

// lt must equal the inverse of the signed comparison.
    check_lt_definition: assert property (
        @(posedge clk) lt == (~a[7] & b[7])
    );

// eq must equal the bitwise equality of the two inputs.
    check_eq_definition: assert property (
        @(posedge clk) eq == (a == b)
    );

// Exactly one of gt, lt, or eq must be asserted.
    check_outputs_onehot: assert property (
        @(posedge clk) $onehot({gt, lt, eq})
    );

// When a is greater than b, only gt can be asserted.
    check_gt_only_when_a_gt_b: assert property (
        @(posedge clk) (a > b) |-> (gt && !lt && !eq)
    );

// When a is less than b, only lt can be asserted.
    check_lt_only_when_a_lt_b: assert property (
        @(posedge clk) (a < b) |-> (lt && !gt && !eq)
    );

// When a equals b, only eq can be asserted.
    check_eq_only_when_a_eq_b: assert property (
        @(posedge clk) (a == b) |-> (eq && !gt && !lt)
    );

// When a and b differ in sign, neither gt nor lt can be asserted.
    check_sign_mismatch_blocks_gt_lt: assert property (
        @(posedge clk) (a[7] != b[7]) |-> (!gt && !lt)
    );

// When a and b are equal in sign, neither eq nor the other outputs can be asserted.
    check_same_sign_blocks_eq: assert property (
        @(posedge clk) (a[7] == b[7]) |-> (!eq && !gt && !lt)
    );

endmodule
