module my_module_sva (
    input logic CLK,
    input logic X,
    input logic A1,
    input logic A2,
    input logic A3,
    input logic A4,
    input logic B1
);
    // X equals (A1&A2&A3&A4) OR B1.
    check_function_equivalence: assert property (
        @(posedge CLK) X == ((A1 & A2 & A3 & A4) | B1)
    );

    // B1 HIGH forces X HIGH.
    check_B1_dominates: assert property (
        @(posedge CLK) (!B1) || (X == 1'b1)
    );

    // All A's HIGH forces X HIGH.
    check_all_As_high_implies_X_high: assert property (
        @(posedge CLK) (!(A1 & A2 & A3 & A4)) || (X == 1'b1)
    );

    // When B1 is LOW, X equals A1&A2&A3&A4.
    check_B1_low_selects_AND: assert property (
        @(posedge CLK) B1 || (X == (A1 & A2 & A3 & A4))
    );

    // X HIGH implies either B1 HIGH or all A's HIGH.
    check_X_high_has_valid_cause: assert property (
        @(posedge CLK) (!X) || (B1 || (A1 & A2 & A3 & A4))
    );

    // X LOW implies B1 LOW and not all A's HIGH.
    check_X_low_means_both_terms_low: assert property (
        @(posedge CLK) X || ((!B1) && !(A1 & A2 & A3 & A4))
    );

    // If all A's are LOW, X equals B1.
    check_all_As_low_passthrough_B1: assert property (
        @(posedge CLK) (!A1 && !A2 && !A3 && !A4) |-> (X == B1)
    );

    // If B1 is LOW and any A is LOW, X must be LOW.
    check_any_A_low_with_B1_low_forces_X_low: assert property (
        @(posedge CLK) (!B1 && (!(A1 & A2 & A3 & A4))) |-> (X == 1'b0)
    );
endmodule