module combinational_logic_sva (
    input A1,
    input A2,
    input A3,
    input B1,
    input VPB,
    input X,
    input VPWR,
    input VGND,
    input VNB
);
    ///// Combinational function checks (clocked on A1 for sampling) /////
    // X matches the defined boolean function of inputs.
    check_x_function_equivalence: assert property (
        @(posedge A1) X == ((A1 && A2 && A3) || (B1 && VPB))
    );

    // When all A inputs are HIGH, X must be HIGH.
    check_a_term_drives_x: assert property (
        @(posedge A1) (A1 && A2 && A3) |-> (X == 1'b1)
    );

    // When B1 and VPB are HIGH, X must be HIGH.
    check_b_term_drives_x: assert property (
        @(posedge A1) (B1 && VPB) |-> (X == 1'b1)
    );

    // When both product terms are LOW, X must be LOW.
    check_x_zero_when_no_term: assert property (
        @(posedge A1) (!((A1 && A2 && A3) || (B1 && VPB))) |-> (X == 1'b0)
    );

    // If X is HIGH, at least one product term must be HIGH.
    check_x_high_implies_term_true: assert property (
        @(posedge A1) X |-> ((A1 && A2 && A3) || (B1 && VPB))
    );

    // If X is LOW, both product terms must be LOW.
    check_x_low_implies_both_terms_low: assert property (
        @(posedge A1) (!X) |-> (!((A1 && A2 && A3)) && !(B1 && VPB))
    );
endmodule