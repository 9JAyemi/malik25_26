module my_module_sva (
    input logic X,
    input logic A1,
    input logic A2,
    input logic A3,
    input logic B1,
    input logic B2
);
    // X equals (A1 & A2 & A3) OR (B1 & B2).
    check_functional_equivalence: assert property (
        @(posedge $global_clock) disable iff (1'b0)
        X == ((A1 && A2 && A3) || (B1 && B2))
    );

    // If A1&A2&A3 are all HIGH, X must be HIGH.
    check_termA_implies_X: assert property (
        @(posedge $global_clock) disable iff (1'b0)
        (A1 && A2 && A3) |-> (X == 1'b1)
    );

    // If B1&B2 are both HIGH, X must be HIGH.
    check_termB_implies_X: assert property (
        @(posedge $global_clock) disable iff (1'b0)
        (B1 && B2) |-> (X == 1'b1)
    );

    // If X is HIGH, at least one product term is HIGH.
    check_X_implies_termA_or_termB: assert property (
        @(posedge $global_clock) disable iff (1'b0)
        X |-> ((A1 && A2 && A3) || (B1 && B2))
    );

    // If both product terms are LOW, X must be LOW.
    check_neither_term_implies_X0: assert property (
        @(posedge $global_clock) disable iff (1'b0)
        (!(A1 && A2 && A3) && !(B1 && B2)) |-> (X == 1'b0)
    );

    // X can only change when at least one input changes.
    check_x_change_requires_input_change: assert property (
        @(posedge $global_clock) disable iff (1'b0)
        $changed(X) |-> ($changed(A1) || $changed(A2) || $changed(A3) || $changed(B1) || $changed(B2))
    );

    // If all inputs are stable, X must remain stable.
    check_inputs_stable_implies_x_stable: assert property (
        @(posedge $global_clock) disable iff (1'b0)
        !($changed(A1) || $changed(A2) || $changed(A3) || $changed(B1) || $changed(B2)) |-> !$changed(X)
    );

    // If only A1 toggles, X toggles iff A2&A3 are HIGH and B1&B2 are LOW.
    check_only_A1_toggle_effect: assert property (
        @(posedge $global_clock) disable iff (1'b0)
        ($changed(A1) && !$changed(A2) && !$changed(A3) && !$changed(B1) && !$changed(B2))
            |-> ($changed(X) == (A2 && A3 && !(B1 && B2)))
    );

    // If only A2 toggles, X toggles iff A1&A3 are HIGH and B1&B2 are LOW.
    check_only_A2_toggle_effect: assert property (
        @(posedge $global_clock) disable iff (1'b0)
        (!$changed(A1) && $changed(A2) && !$changed(A3) && !$changed(B1) && !$changed(B2))
            |-> ($changed(X) == (A1 && A3 && !(B1 && B2)))
    );

    // If only B1 toggles, X toggles iff B2 is HIGH and A1&A2&A3 are LOW as a group.
    check_only_B1_toggle_effect: assert property (
        @(posedge $global_clock) disable iff (1'b0)
        (!$changed(A1) && !$changed(A2) && !$changed(A3) && $changed(B1) && !$changed(B2))
            |-> ($changed(X) == (B2 && !(A1 && A2 && A3)))
    );

endmodule