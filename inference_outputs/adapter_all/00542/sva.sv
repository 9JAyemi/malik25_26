module my_module_sva (
    input logic X,
    input logic A1,
    input logic A2,
    input logic A3,
    input logic B1,
    input logic VPWR,
    input logic VGND,
    input logic VPB,
    input logic VNB
);

    // X must equal the OR of B1 and the three-input AND of A1, A2, and A3.
    check_x_matches_or_of_and: assert property (
        @($global_clock) X == (B1 | (A1 & A2 & A3))
    );

    // B1 high must force X high.
    check_b1_forces_x_high: assert property (
        @($global_clock) B1 |-> X
    );

    // All three A inputs high must force X high.
    check_all_a_high_forces_x_high: assert property (
        @($global_clock) (A1 & A2 & A3) |-> X
    );

    // With B1 low and not all A inputs high, X must be low.
    check_no_active_term_keeps_x_low: assert property (
        @($global_clock) (!B1 && !(A1 & A2 & A3)) |-> !X
    );

    // A high X must come from B1 or the three-input AND term.
    check_x_high_has_valid_cause: assert property (
        @($global_clock) X |-> (B1 || (A1 & A2 & A3))
    );

    // If X is low, B1 must be low and not all A inputs can be high.
    check_x_low_has_valid_cause: assert property (
        @($global_clock) !X |-> (!B1 && !(A1 & A2 & A3))
    );

    // X can change only if B1 or the three-input AND term changes.
    check_x_change_has_valid_cause: assert property (
        @($global_clock) $changed(X) |-> ($changed(B1) || $changed(A1 & A2 & A3))
    );

endmodule