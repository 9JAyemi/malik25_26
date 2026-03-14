module boolean_module_sva (
    input logic clk,
    input logic A,
    input logic B,
    input logic C,
    input logic D,
    input logic X
);

    // X equals the Boolean function (A & B) | (C & D).
    check_functional_equivalence: assert property (
        @(posedge clk) X === ((A & B) | (C & D))
    );

    // When A and B are both 1, X must be 1.
    check_ab_true_implies_x1: assert property (
        @(posedge clk) (A === 1'b1 && B === 1'b1) |-> (X === 1'b1)
    );

    // When C and D are both 1, X must be 1.
    check_cd_true_implies_x1: assert property (
        @(posedge clk) (C === 1'b1 && D === 1'b1) |-> (X === 1'b1)
    );

    // If X is 1, at least one product term (A&B or C&D) is 1.
    check_x1_requires_some_term1: assert property (
        @(posedge clk) (X === 1'b1) |-> (((A & B) === 1'b1) || ((C & D) === 1'b1))
    );

    // If both (A&B) and (C&D) are 0, X must be 0.
    check_terms_zero_implies_x0: assert property (
        @(posedge clk) (((A & B) === 1'b0) && ((C & D) === 1'b0)) |-> (X === 1'b0)
    );

    // If X is 0, both (A&B) and (C&D) are 0.
    check_x0_requires_terms_zero: assert property (
        @(posedge clk) (X === 1'b0) |-> (((A & B) === 1'b0) && ((C & D) === 1'b0))
    );

    // If inputs A,B,C,D are stable across a cycle, X is stable.
    check_output_stable_if_inputs_stable: assert property (
        @(posedge clk) $stable({A,B,C,D}) |-> $stable(X)
    );

    // A&B rising with C&D=0 forces X=1 in the same cycle.
    check_ab_rise_causes_x1_when_cd0: assert property (
        @(posedge clk) $rose(A & B) && ((C & D) === 1'b0) |-> (X === 1'b1)
    );

    // C&D rising with A&B=0 forces X=1 in the same cycle.
    check_cd_rise_causes_x1_when_ab0: assert property (
        @(posedge clk) $rose(C & D) && ((A & B) === 1'b0) |-> (X === 1'b1)
    );

    // A&B falling with C&D=0 forces X=0 in the same cycle.
    check_ab_fall_causes_x0_when_cd0: assert property (
        @(posedge clk) $fell(A & B) && ((C & D) === 1'b0) |-> (X === 1'b0)
    );

endmodule