module sky130_fd_sc_ls__a211o_sva (
    input logic X,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic C1
);
    // X equals (A1 & A2) OR B1 OR C1.
    check_functional_equivalence: assert property (
        @($global_clock) X == ((A1 & A2) | B1 | C1)
    );

    // When B1 is HIGH, X must be HIGH.
    check_b1_dominates: assert property (
        @($global_clock) B1 |-> X
    );

    // When C1 is HIGH, X must be HIGH.
    check_c1_dominates: assert property (
        @($global_clock) C1 |-> X
    );

    // With B1=C1=0, X equals A1 & A2.
    check_no_b1c1_then_and_only: assert property (
        @($global_clock) (!B1 && !C1) |-> (X == (A1 & A2))
    );

    // When A1&A2 are both HIGH, X must be HIGH.
    check_and_implies_x: assert property (
        @($global_clock) (A1 & A2) |-> X
    );

    // If X is LOW, then B1=0, C1=0, and A1&A2=0.
    check_x_zero_implies_terms_zero: assert property (
        @($global_clock) (!X) |-> (!B1 && !C1 && !(A1 & A2))
    );

    // All inputs LOW implies X is LOW.
    check_all_zero_implies_x_zero: assert property (
        @($global_clock) (!A1 && !A2 && !B1 && !C1) |-> (!X)
    );

    // If all inputs are stable, X is stable.
    check_stability_when_inputs_stable: assert property (
        @($global_clock) $stable(A1) && $stable(A2) && $stable(B1) && $stable(C1) |-> $stable(X)
    );

    // Rising B1 forces X HIGH in the same cycle.
    check_b1_rise_forces_x_high: assert property (
        @($global_clock) $rose(B1) |-> X
    );

    // Rising C1 forces X HIGH in the same cycle.
    check_c1_rise_forces_x_high: assert property (
        @($global_clock) $rose(C1) |-> X
    );

    // With B1=C1=0, a rise of (A1&A2) forces X HIGH.
    check_and_rise_forces_x_high_no_b1c1: assert property (
        @($global_clock) (!B1 && !C1 && $rose(A1 & A2)) |-> X
    );

    // With C1=0 and A1&A2=0, a fall of B1 forces X LOW.
    check_b1_fall_to_zero_when_others_zero: assert property (
        @($global_clock) $fell(B1) && (C1==1'b0) && ((A1 & A2)==1'b0) |-> (X==1'b0)
    );

    // With B1=0 and A1&A2=0, a fall of C1 forces X LOW.
    check_c1_fall_to_zero_when_others_zero: assert property (
        @($global_clock) $fell(C1) && (B1==1'b0) && ((A1 & A2)==1'b0) |-> (X==1'b0)
    );
endmodule