module comparator_sva (
    input logic        clk,
    input logic [3:0]  A,
    input logic [3:0]  B,
    input logic        EQ,
    input logic        GT
);

    // No reset is present in the RTL.
    // The DUT is combinational, so checks are sampled on clk.

    // EQ must match the implemented zero-detect of A-B.
    check_eq_matches_rtl_expression: assert property (
        @(posedge clk) EQ == (&(~(A - B)))
    );

    // EQ must assert when A and B are equal.
    check_eq_when_inputs_equal: assert property (
        @(posedge clk) (A == B) |-> (EQ == 1'b1)
    );

    // EQ must deassert when A and B are different.
    check_eq_when_inputs_different: assert property (
        @(posedge clk) (A != B) |-> (EQ == 1'b0)
    );

    // GT is tied low by the RTL logic.
    check_gt_tied_low: assert property (
        @(posedge clk) GT == 1'b0
    );

endmodule