module comparator_sva (
    input logic clk,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic EQ,
    input logic GT,
    input logic LT
);
    // No clock/reset in DUT; combinational. Assertions sample on external clk with no reset gating.
    // Behavior: EQ iff A==B, GT iff A>B, LT iff A<B; exactly one output is HIGH.

    // Outputs EQ and GT are mutually exclusive.
    check_mutex_eq_gt: assert property (
        @(posedge clk) !(EQ && GT)
    );

    // Outputs EQ and LT are mutually exclusive.
    check_mutex_eq_lt: assert property (
        @(posedge clk) !(EQ && LT)
    );

    // Outputs GT and LT are mutually exclusive.
    check_mutex_gt_lt: assert property (
        @(posedge clk) !(GT && LT)
    );

    // At least one of EQ/GT/LT must be HIGH.
    check_not_all_zero: assert property (
        @(posedge clk) (EQ || GT || LT)
    );

    // When A equals B, outputs reflect equality.
    check_map_equal: assert property (
        @(posedge clk) (A == B) |-> (EQ && !GT && !LT)
    );

    // When A is greater than B, outputs reflect greater-than.
    check_map_greater: assert property (
        @(posedge clk) (A > B) |-> (!EQ && GT && !LT)
    );

    // When A is less than B, outputs reflect less-than.
    check_map_less: assert property (
        @(posedge clk) (A < B) |-> (!EQ && !GT && LT)
    );

    // If EQ is HIGH, inputs must be equal.
    check_eq_implies_relation: assert property (
        @(posedge clk) EQ |-> (A == B)
    );

    // If GT is HIGH, A must be greater than B.
    check_gt_implies_relation: assert property (
        @(posedge clk) GT |-> (A > B)
    );

    // If LT is HIGH, A must be less than B.
    check_lt_implies_relation: assert property (
        @(posedge clk) LT |-> (A < B)
    );
endmodule