module verilog_module_sva (
    input logic A1,
    input logic A2,
    input logic B1,
    input logic C1,
    input logic X,
    input logic VPB,
    input logic VPWR,
    input logic VGND,
    input logic VNB
);

    // X must equal (A1 & A2) | (B1 & C1).
    check_x_or_of_ands: assert property (
        @(posedge A1 or posedge A2 or posedge B1 or posedge C1 or posedge X or posedge VPB or posedge VPWR or posedge VGND or posedge VNB)
            X == ((A1 & A2) | (B1 & C1))
    );

    // If A1&A2 is 1 then X must be 1.
    check_a_term_implies_x: assert property (
        @(posedge A1 or posedge A2 or posedge B1 or posedge C1 or posedge X or posedge VPB or posedge VPWR or posedge VGND or posedge VNB)
            (A1 && A2) |-> (X == 1'b1)
    );

    // If B1&C1 is 1 then X must be 1.
    check_b_term_implies_x: assert property (
        @(posedge A1 or posedge A2 or posedge B1 or posedge C1 or posedge X or posedge VPB or posedge VPWR or posedge VGND or posedge VNB)
            (B1 && C1) |-> (X == 1'b1)
    );

    // If X is 1 then at least one product term is 1.
    check_x_one_implies_some_term: assert property (
        @(posedge A1 or posedge A2 or posedge B1 or posedge C1 or posedge X or posedge VPB or posedge VPWR or posedge VGND or posedge VNB)
            (X == 1'b1) |-> ((A1 && A2) || (B1 && C1))
    );

    // If X is 0 then both product terms are 0.
    check_x_zero_implies_no_terms: assert property (
        @(posedge A1 or posedge A2 or posedge B1 or posedge C1 or posedge X or posedge VPB or posedge VPWR or posedge VGND or posedge VNB)
            (X == 1'b0) |-> ((! (A1 && A2)) && (! (B1 && C1)))
    );

    // If both product terms are 0 then X is 0.
    check_x_zero_when_no_terms_true: assert property (
        @(posedge A1 or posedge A2 or posedge B1 or posedge C1 or posedge X or posedge VPB or posedge VPWR or posedge VGND or posedge VNB)
            ((! (A1 && A2)) && (! (B1 && C1))) |-> (X == 1'b0)
    );

    // If all four inputs are 0 then X is 0.
    check_x_zero_when_all_zero: assert property (
        @(posedge A1 or posedge A2 or posedge B1 or posedge C1 or posedge X or posedge VPB or posedge VPWR or posedge VGND or posedge VNB)
            ((A1 == 1'b0) && (A2 == 1'b0) && (B1 == 1'b0) && (C1 == 1'b0)) |-> (X == 1'b0)
    );

    // If A1 and B1 are 0 then X is 0.
    check_x_zero_when_a1_b1_zero: assert property (
        @(posedge A1 or posedge A2 or posedge B1 or posedge C1 or posedge X or posedge VPB or posedge VPWR or posedge VGND or posedge VNB)
            ((A1 == 1'b0) && (B1 == 1'b0)) |-> (X == 1'b0)
    );

    // If A2 and C1 are 0 then X is 0.
    check_x_zero_when_a2_c1_zero: assert property (
        @(posedge A1 or posedge A2 or posedge B1 or posedge C1 or posedge X or posedge VPB or posedge VPWR or posedge VGND or posedge VNB)
            ((A2 == 1'b0) && (C1 == 1'b0)) |-> (X == 1'b0)
    );

    // If both product terms are 1 then X is 1.
    check_x_one_when_both_terms_true: assert property (
        @(posedge A1 or posedge A2 or posedge B1 or posedge C1 or posedge X or posedge VPB or posedge VPWR or posedge VGND or posedge VNB)
            ((A1 && A2) && (B1 && C1)) |-> (X == 1'b1)
    );

    // When B-path is off, X equals A1&A2.
    check_x_equals_a_term_when_b_off: assert property (
        @(posedge A1 or posedge A2 or posedge B1 or posedge C1 or posedge X or posedge VPB or posedge VPWR or posedge VGND or posedge VNB)
            ((B1 == 1'b0) || (C1 == 1'b0)) |-> (X == (A1 & A2))
    );

    // When A-path is off, X equals B1&C1.
    check_x_equals_b_term_when_a_off: assert property (
        @(posedge A1 or posedge A2 or posedge B1 or posedge C1 or posedge X or posedge VPB or posedge VPWR or posedge VGND or posedge VNB)
            ((A1 == 1'b0) || (A2 == 1'b0)) |-> (X == (B1 & C1))
    );

    // X does not change if A1,A2,B1,C1 are stable.
    check_x_stable_when_inputs_stable: assert property (
        @(posedge A1 or posedge A2 or posedge B1 or posedge C1 or posedge X or negedge X or posedge VPB or posedge VPWR or posedge VGND or posedge VNB)
            $stable({A1, A2, B1, C1}) |-> $stable(X)
    );

endmodule