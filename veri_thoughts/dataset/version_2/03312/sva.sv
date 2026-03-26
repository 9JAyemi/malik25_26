module comparator_4bit_sva(
    input logic clk,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic [3:0] C,
    input logic [3:0] D,
    input logic EQ,
    input logic GT
);

    // No reset is present in the RTL; sample combinational behavior on clk.

    // EQ is high exactly when all four inputs are equal.
    check_eq_definition: assert property (
        @(posedge clk) EQ === ((A == B) && (B == C) && (C == D))
    );

    // GT is high exactly for strict descending order or the all-equal case.
    check_gt_definition: assert property (
        @(posedge clk) GT === (((A > B) && (B > C) && (C > D)) || ((A == B) && (B == C) && (C == D)))
    );

    // All equal inputs drive both EQ and GT high.
    check_all_equal_outputs_high: assert property (
        @(posedge clk) ((A == B) && (B == C) && (C == D)) |-> ((EQ === 1'b1) && (GT === 1'b1))
    );

    // Strict descending inputs drive GT high and EQ low.
    check_strict_descending_outputs: assert property (
        @(posedge clk) ((A > B) && (B > C) && (C > D)) |-> ((GT === 1'b1) && (EQ === 1'b0))
    );

    // EQ can only be high when GT is also high.
    check_eq_implies_gt: assert property (
        @(posedge clk) (EQ === 1'b1) |-> (GT === 1'b1)
    );

    // GT without EQ means the inputs are strictly descending.
    check_gt_without_eq_means_descending: assert property (
        @(posedge clk) ((GT === 1'b1) && (EQ === 1'b0)) |-> ((A > B) && (B > C) && (C > D))
    );

    // Any break in the equality chain keeps EQ low.
    check_mismatch_clears_eq: assert property (
        @(posedge clk) !((A == B) && (B == C) && (C == D)) |-> (EQ === 1'b0)
    );

    // Inputs outside the two GT cases keep GT low.
    check_nonqualifying_inputs_clear_gt: assert property (
        @(posedge clk) !(((A > B) && (B > C) && (C > D)) || ((A == B) && (B == C) && (C == D))) |-> (GT === 1'b0)
    );

endmodule