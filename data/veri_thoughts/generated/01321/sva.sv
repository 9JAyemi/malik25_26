module sky130_fd_sc_ls__and4_sva (
    input logic CLK,  // external sampling clock (RTL has no clock)
    input logic X,
    input logic A,
    input logic B,
    input logic C,
    input logic D
);
    // Function: X equals A & B & C & D at every sample.
    check_function_equivalence: assert property (
        @(posedge CLK) X == (A & B & C & D)
    );

    // When X is HIGH, all inputs must be HIGH.
    check_x_high_implies_all_high: assert property (
        @(posedge CLK) (X == 1'b1) |-> (A && B && C && D)
    );

    // When all inputs are HIGH, X must be HIGH.
    check_all_inputs_high_implies_x_high: assert property (
        @(posedge CLK) (A && B && C && D) |-> (X == 1'b1)
    );

    // A rising edge on X requires all inputs HIGH in the same cycle.
    check_rose_x_requires_all_high: assert property (
        @(posedge CLK) $rose(X) |-> (A && B && C && D)
    );

    // A falling edge on X requires at least one input LOW in the same cycle.
    check_fell_x_requires_some_low: assert property (
        @(posedge CLK) $fell(X) |-> !(A && B && C && D)
    );

    // Transition from not-all-high to all-high must cause X to rise.
    check_all_high_transition_causes_rose_x: assert property (
        @(posedge CLK) (!$past(A && B && C && D) && (A && B && C && D)) |-> $rose(X)
    );

    // Transition from all-high to not-all-high must cause X to fall.
    check_all_high_to_not_all_transition_causes_fall_x: assert property (
        @(posedge CLK) ($past(A && B && C && D) && !(A && B && C && D)) |-> $fell(X)
    );

    // If all inputs are stable across a cycle, X must be stable.
    check_inputs_stable_implies_x_stable: assert property (
        @(posedge CLK) ($stable(A) && $stable(B) && $stable(C) && $stable(D)) |-> $stable(X)
    );

    // If X changes, at least one input must have changed.
    check_x_change_requires_input_change: assert property (
        @(posedge CLK) $changed(X) |-> ($changed(A) || $changed(B) || $changed(C) || $changed(D))
    );
endmodule