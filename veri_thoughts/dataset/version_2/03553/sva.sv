module my_module_sva (
    input logic clk,
    input logic A1,
    input logic A2,
    input logic A3,
    input logic A4,
    input logic B1,
    input logic X
);

    // When both input pairs compare equal, X follows B1.
    check_true_branch_selects_b1: assert property (
        @(posedge clk) (((A1 == A2) && (A3 == A4)) === 1'b1) |-> (X == B1)
    );

    // When either input pair does not compare equal, X follows A1 & A2.
    check_false_branch_selects_a1_a2_and: assert property (
        @(posedge clk) (((A1 == A2) && (A3 == A4)) !== 1'b1) |-> (X == (A1 & A2))
    );

    // In the AND branch, a low A1 forces X low.
    check_false_branch_a1_low_forces_zero: assert property (
        @(posedge clk) ((((A1 == A2) && (A3 == A4)) !== 1'b1) && (A1 == 1'b0)) |-> (X == 1'b0)
    );

    // In the AND branch, a low A2 forces X low.
    check_false_branch_a2_low_forces_zero: assert property (
        @(posedge clk) ((((A1 == A2) && (A3 == A4)) !== 1'b1) && (A2 == 1'b0)) |-> (X == 1'b0)
    );

    // In the AND branch, high A1 and A2 drive X high.
    check_false_branch_both_high_drive_one: assert property (
        @(posedge clk) ((((A1 == A2) && (A3 == A4)) !== 1'b1) && (A1 == 1'b1) && (A2 == 1'b1)) |-> (X == 1'b1)
    );

endmodule