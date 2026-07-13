module and_or_sva (
    input logic CLK,  // external clock for sampling assertions
    input logic A,
    input logic B,
    input logic C,
    input logic D,
    input logic Y
);
    // DUT is purely combinational with no reset; use disable iff (1'b0).

    // Y equals A|B|D (absorbing (A&B&C) into A|B).
    check_y_function_equivalence: assert property (
        @(posedge CLK) disable iff (1'b0) Y === (A | B | D)
    );

    // Y must be 1 whenever D is 1.
    check_y_high_if_d_high: assert property (
        @(posedge CLK) disable iff (1'b0) D |-> (Y === 1'b1)
    );

    // Y must be 1 whenever A is 1.
    check_y_high_if_a_high: assert property (
        @(posedge CLK) disable iff (1'b0) A |-> (Y === 1'b1)
    );

    // Y must be 1 whenever B is 1.
    check_y_high_if_b_high: assert property (
        @(posedge CLK) disable iff (1'b0) B |-> (Y === 1'b1)
    );

    // With D==0, Y equals A|B.
    check_y_eq_a_or_b_when_d_low: assert property (
        @(posedge CLK) disable iff (1'b0) (D === 1'b0) |-> (Y === (A | B))
    );

    // With A==0 and B==0, Y equals D.
    check_y_eq_d_when_a_b_low: assert property (
        @(posedge CLK) disable iff (1'b0) (A === 1'b0) && (B === 1'b0) |-> (Y === D)
    );

    // With B==0 and D==0, Y equals A.
    check_y_eq_a_when_b_d_low: assert property (
        @(posedge CLK) disable iff (1'b0) (B === 1'b0) && (D === 1'b0) |-> (Y === A)
    );

    // With A==0 and D==0, Y equals B.
    check_y_eq_b_when_a_d_low: assert property (
        @(posedge CLK) disable iff (1'b0) (A === 1'b0) && (D === 1'b0) |-> (Y === B)
    );

    // If A,B,D are stable, Y must be stable (C has no effect).
    check_y_stable_when_abd_stable: assert property (
        @(posedge CLK) disable iff (1'b0) $stable(A) && $stable(B) && $stable(D) |-> $stable(Y)
    );

    // Changes on C alone cannot change Y.
    check_c_independence: assert property (
        @(posedge CLK) disable iff (1'b0) $changed(C) && $stable(A) && $stable(B) && $stable(D) |-> $stable(Y)
    );

    // Y rising requires at least one of A,B,D to be 1.
    check_y_rise_requires_input_high: assert property (
        @(posedge CLK) disable iff (1'b0) $rose(Y) |-> (A || B || D)
    );

    // Y falling requires A,B,D all 0.
    check_y_fall_requires_inputs_low: assert property (
        @(posedge CLK) disable iff (1'b0) $fell(Y) |-> (!A && !B && !D)
    );
endmodule