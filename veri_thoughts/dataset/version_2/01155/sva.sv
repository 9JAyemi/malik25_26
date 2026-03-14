module and4_2and_sva (
    input logic CLK, // sampling clock for assertions (RTL has no clock)
    input logic A,
    input logic B,
    input logic C,
    input logic D,
    input logic X
);
    ///// Functional equivalence /////
    // X equals the 4-input AND of A,B,C,D.
    check_and_equivalence: assert property (
        @(posedge CLK) X == (A & B & C & D)
    );

    ///// Output transition conditions /////
    // X can rise only when all inputs are HIGH.
    check_x_rise_requires_all_high: assert property (
        @(posedge CLK) $rose(X) |-> (A & B & C & D)
    );
    // X can fall only when not all inputs are HIGH.
    check_x_fall_requires_some_low: assert property (
        @(posedge CLK) $fell(X) |-> !(A & B & C & D)
    );

    ///// Zero domination (any LOW input forces X LOW) /////
    // A=0 forces X=0.
    check_zero_dom_A: assert property (
        @(posedge CLK) (!A) |-> (!X)
    );
    // B=0 forces X=0.
    check_zero_dom_B: assert property (
        @(posedge CLK) (!B) |-> (!X)
    );
    // C=0 forces X=0.
    check_zero_dom_C: assert property (
        @(posedge CLK) (!C) |-> (!X)
    );
    // D=0 forces X=0.
    check_zero_dom_D: assert property (
        @(posedge CLK) (!D) |-> (!X)
    );

    ///// Input-driven rising behavior /////
    // If A rises and B,C,D are HIGH, X must rise.
    check_rise_when_A_rises_and_others_high: assert property (
        @(posedge CLK) ($rose(A) && B && C && D) |-> $rose(X)
    );
    // If B rises and A,C,D are HIGH, X must rise.
    check_rise_when_B_rises_and_others_high: assert property (
        @(posedge CLK) ($rose(B) && A && C && D) |-> $rose(X)
    );
    // If C rises and A,B,D are HIGH, X must rise.
    check_rise_when_C_rises_and_others_high: assert property (
        @(posedge CLK) ($rose(C) && A && B && D) |-> $rose(X)
    );
endmodule