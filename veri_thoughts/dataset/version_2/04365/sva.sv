module math_op_assertions (
    input logic clk,
    input logic A,
    input logic B,
    input logic C,
    input logic X
);

    // Output must match the implemented combinational function.
    check_output_boolean_form: assert property (
        @(posedge clk) X == (A & (B | C))
    );

    // When A<B for 1-bit inputs, the output must be zero.
    check_lt_branch_forces_zero: assert property (
        @(posedge clk) (!A && B) |-> (X == 1'b0)
    );

    // When A>B for 1-bit inputs, the output must match C.
    check_gt_branch_matches_c: assert property (
        @(posedge clk) (A && !B) |-> (X == C)
    );

    // When A and B are both zero, the equality branch drives zero.
    check_eq_low_branch_forces_zero: assert property (
        @(posedge clk) (!A && !B) |-> (X == 1'b0)
    );

    // When A and B are both one, the equality branch drives one.
    check_eq_high_branch_sets_one: assert property (
        @(posedge clk) (A && B) |-> (X == 1'b1)
    );

endmodule