module sky130_fd_sc_hvl__lsbuflv2hv_clkiso_hlkg_sva (
    input  logic CLK,      // sampling clock for assertions
    input  logic X,
    input  logic A,
    input  logic SLEEP_B
);
    // Combinational function: X equals A AND SLEEP_B.
    check_functional_and: assert property (
        @(posedge CLK) (X == (A & SLEEP_B))
    );

    // When SLEEP_B is LOW, X must be LOW.
    check_sleep_b_low_forces_low: assert property (
        @(posedge CLK) (!SLEEP_B) |-> (X == 1'b0)
    );

    // When SLEEP_B is HIGH, X equals A.
    check_sleep_b_high_transparent: assert property (
        @(posedge CLK) (SLEEP_B) |-> (X == A)
    );

    // When A is LOW, X must be LOW.
    check_a_low_forces_low: assert property (
        @(posedge CLK) (!A) |-> (X == 1'b0)
    );

    // X HIGH implies both A and SLEEP_B are HIGH.
    check_x_high_implies_inputs_high: assert property (
        @(posedge CLK) (X == 1'b1) |-> (A && SLEEP_B)
    );

    // With SLEEP_B HIGH, a rising A causes X to rise the same cycle.
    check_a_rise_propagates_when_enabled: assert property (
        @(posedge CLK) (SLEEP_B && $rose(A)) |-> $rose(X)
    );

    // With SLEEP_B HIGH, a falling A causes X to fall the same cycle.
    check_a_fall_propagates_when_enabled: assert property (
        @(posedge CLK) (SLEEP_B && $fell(A)) |-> $fell(X)
    );

    // X rising requires both A and SLEEP_B HIGH.
    check_x_rise_requires_enabled_and_a: assert property (
        @(posedge CLK) $rose(X) |-> (A && SLEEP_B)
    );

    // X falling requires A LOW or SLEEP_B LOW.
    check_x_fall_requires_either_low: assert property (
        @(posedge CLK) $fell(X) |-> ((!A) || (!SLEEP_B))
    );

    // If A and SLEEP_B do not change, X does not change.
    check_x_stable_when_inputs_stable: assert property (
        @(posedge CLK) (!$changed(A) && !$changed(SLEEP_B)) |-> (!$changed(X))
    );

    // On SLEEP_B rising, X equals A in the same cycle.
    check_enable_rise_sets_x_equal_a: assert property (
        @(posedge CLK) $rose(SLEEP_B) |-> (X == A)
    );

    // On SLEEP_B falling, X is forced LOW in the same cycle.
    check_enable_fall_forces_x_low: assert property (
        @(posedge CLK) $fell(SLEEP_B) |-> (X == 1'b0)
    );
endmodule