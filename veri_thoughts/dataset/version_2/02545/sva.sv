module sky130_fd_sc_hd__and2_sva (
    input logic CLK,
    input logic X,
    input logic A,
    input logic B
);
    // X equals A AND B each cycle.
    check_and_equivalence: assert property (
        @(posedge CLK) X == (A & B)
    );

    // If X is HIGH, both inputs are HIGH.
    check_x_high_implies_inputs_high: assert property (
        @(posedge CLK) (X == 1'b1) |-> (A == 1'b1) && (B == 1'b1)
    );

    // If A is LOW, X must be LOW.
    check_a_low_forces_x_low: assert property (
        @(posedge CLK) (A == 1'b0) |-> (X == 1'b0)
    );

    // If B is LOW, X must be LOW.
    check_b_low_forces_x_low: assert property (
        @(posedge CLK) (B == 1'b0) |-> (X == 1'b0)
    );

    // If both inputs are HIGH, X must be HIGH.
    check_inputs_high_force_x_high: assert property (
        @(posedge CLK) (A == 1'b1 && B == 1'b1) |-> (X == 1'b1)
    );

    // Output rises only when at least one input rises.
    check_x_rise_requires_input_rise: assert property (
        @(posedge CLK) $rose(X) |-> ($rose(A) || $rose(B))
    );

    // When X rises, both inputs are HIGH that cycle.
    check_x_rise_inputs_high_now: assert property (
        @(posedge CLK) $rose(X) |-> (A == 1'b1) && (B == 1'b1)
    );

    // Output falls only when at least one input falls.
    check_x_fall_requires_input_fall: assert property (
        @(posedge CLK) $fell(X) |-> ($fell(A) || $fell(B))
    );

    // When X falls, at least one input is LOW that cycle.
    check_x_fall_inputs_low_now: assert property (
        @(posedge CLK) $fell(X) |-> (!A || !B)
    );

    // If both inputs are stable, the output is stable.
    check_stability_with_stable_inputs: assert property (
        @(posedge CLK) ($stable(A) && $stable(B)) |-> $stable(X)
    );

    // Output changes only if some input changes.
    check_x_change_requires_input_change: assert property (
        @(posedge CLK) $changed(X) |-> ($changed(A) || $changed(B))
    );
endmodule