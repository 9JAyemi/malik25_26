module sky130_fd_sc_ms__a211o_sva (
    input logic CLK,
    input logic X,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic C1
);
    // Analysis: no clock/reset in RTL; pure combinational cell: X = (A1 & A2) | B1 | C1.

    // X equals OR of B1, C1, and (A1 & A2).
    check_function_equation: assert property (
        @(posedge CLK) X == ((A1 & A2) | B1 | C1)
    );

    // If B1 is HIGH, X must be HIGH.
    check_B1_forces_X: assert property (
        @(posedge CLK) B1 |-> X
    );

    // If C1 is HIGH, X must be HIGH.
    check_C1_forces_X: assert property (
        @(posedge CLK) C1 |-> X
    );

    // If both A1 and A2 are HIGH, X must be HIGH.
    check_A1A2_force_X: assert property (
        @(posedge CLK) (A1 & A2) |-> X
    );

    // If X is LOW, then B1 and C1 are LOW and not(A1 & A2).
    check_X_low_implies_terms_low: assert property (
        @(posedge CLK) !X |-> (!B1 && !C1 && !(A1 & A2))
    );

    // When B1 and C1 are LOW, X equals (A1 & A2).
    check_when_B1C1_low_X_equals_A1A2: assert property (
        @(posedge CLK) (!B1 && !C1) |-> (X == (A1 & A2))
    );

    // When (A1 & A2) is LOW, X equals (B1 | C1).
    check_when_not_A1A2_X_equals_B1_or_C1: assert property (
        @(posedge CLK) (!(A1 & A2)) |-> (X == (B1 | C1))
    );

    // If X is HIGH, at least one product term is HIGH.
    check_X_high_implies_some_term_high: assert property (
        @(posedge CLK) X |-> (B1 || C1 || (A1 & A2))
    );

    // If all inputs are LOW, X must be LOW.
    check_all_inputs_low_implies_X_low: assert property (
        @(posedge CLK) (!A1 && !A2 && !B1 && !C1) |-> (!X)
    );

    // When B1 is LOW, X equals ((A1 & A2) | C1).
    check_when_B1_low_X_equals_A1A2_or_C1: assert property (
        @(posedge CLK) (!B1) |-> (X == ((A1 & A2) | C1))
    );

    // When C1 is LOW, X equals ((A1 & A2) | B1).
    check_when_C1_low_X_equals_A1A2_or_B1: assert property (
        @(posedge CLK) (!C1) |-> (X == ((A1 & A2) | B1))
    );

endmodule