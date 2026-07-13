module my_module_sva (
    input  logic CLK,
    input  logic X,
    input  logic A1,
    input  logic A2,
    input  logic B1,
    input  logic B2,
    input  logic C1
);
    // X equals (A1|A2)&(B1|B2)&C1.
    check_function_equivalence: assert property (
        @(posedge CLK) X === ((A1 || A2) && (B1 || B2) && C1)
    );

    // X high requires C1 high.
    check_x_high_requires_c1: assert property (
        @(posedge CLK) (X == 1'b1) |-> (C1 == 1'b1)
    );

    // X high requires at least one A high.
    check_x_high_requires_a: assert property (
        @(posedge CLK) (X == 1'b1) |-> (A1 || A2)
    );

    // X high requires at least one B high.
    check_x_high_requires_b: assert property (
        @(posedge CLK) (X == 1'b1) |-> (B1 || B2)
    );

    // C1 low forces X low.
    check_c1_low_forces_x_low: assert property (
        @(posedge CLK) (C1 == 1'b0) |-> (X == 1'b0)
    );

    // Both A low forces X low.
    check_a_both_low_forces_x_low: assert property (
        @(posedge CLK) ((A1 == 1'b0) && (A2 == 1'b0)) |-> (X == 1'b0)
    );

    // Both B low forces X low.
    check_b_both_low_forces_x_low: assert property (
        @(posedge CLK) ((B1 == 1'b0) && (B2 == 1'b0)) |-> (X == 1'b0)
    );

    // X can only change if some input changed.
    check_x_change_requires_input_change: assert property (
        @(posedge CLK) $changed(X) |-> ($changed(A1) || $changed(A2) || $changed(B1) || $changed(B2) || $changed(C1))
    );

    // If all inputs are stable, X must be stable.
    check_inputs_stable_hold_x_stable: assert property (
        @(posedge CLK) (!$changed(A1) && !$changed(A2) && !$changed(B1) && !$changed(B2) && !$changed(C1)) |-> !$changed(X)
    );

    // X rising implies all enabling conditions now true.
    check_x_rise_requires_conditions: assert property (
        @(posedge CLK) $rose(X) |-> ((A1 || A2) && (B1 || B2) && (C1 == 1'b1))
    );

    // C1 falling forces X low in the same cycle.
    check_c1_fall_forces_x_low: assert property (
        @(posedge CLK) $fell(C1) |-> (X == 1'b0)
    );

    // With both OR terms true, rising C1 drives X high.
    check_c1_rise_sets_x_high_when_ors_true: assert property (
        @(posedge CLK) ($rose(C1) && (A1 || A2) && (B1 || B2)) |-> (X == 1'b1)
    );
endmodule