module comparator_sva (
    input logic clk,
    input logic [3:0] a,
    input logic [3:0] b,
    input logic gt,
    input logic lt,
    input logic eq
);

// When a > b, outputs must be gt=1, lt=0, eq=0.
    check_gt_when_a_gt_b: assert property (
        @(posedge clk) (a > b) |-> (gt == 1'b1 && lt == 1'b0 && eq == 1'b0)
    );

// When a < b, outputs must be gt=0, lt=1, eq=0.
    check_lt_when_a_lt_b: assert property (
        @(posedge clk) (a < b) |-> (gt == 1'b0 && lt == 1'b1 && eq == 1'b0)
    );

// When a == b, outputs must be gt=0, lt=0, eq=1.
    check_eq_when_a_eq_b: assert property (
        @(posedge clk) (a == b) |-> (gt == 1'b0 && lt == 1'b0 && eq == 1'b1)
    );

// gt can only be 1 when a > b.
    check_gt_only_when_a_gt_b: assert property (
        @(posedge clk) (gt == 1'b1) |-> (a > b)
    );

// lt can only be 1 when a < b.
    check_lt_only_when_a_lt_b: assert property (
        @(posedge clk) (lt == 1'b1) |-> (a < b)
    );

// eq can only be 1 when a == b.
    check_eq_only_when_a_eq_b: assert property (
        @(posedge clk) (eq == 1'b1) |-> (a == b)
    );

// Exactly one of {gt,lt,eq} is 1 at all times.
    check_onehot_outputs: assert property (
        @(posedge clk) $onehot({gt, lt, eq})
    );

endmodule
