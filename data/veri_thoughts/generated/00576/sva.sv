module sky130_fd_sc_hd__lpflow_isobufsrc_sva (
    input logic clk,
    input logic X,
    input logic SLEEP,
    input logic A
);
    // X equals A & ~SLEEP combinationally.
    check_functional_x_equals_a_and_not_sleep: assert property (
        @(posedge clk) X == (A & ~SLEEP)
    );

    // When SLEEP is HIGH, X must be LOW.
    check_sleep_high_forces_x_low: assert property (
        @(posedge clk) (SLEEP == 1'b1) |-> (X == 1'b0)
    );

    // When SLEEP is LOW, X equals A.
    check_sleep_low_makes_x_equal_a: assert property (
        @(posedge clk) (SLEEP == 1'b0) |-> (X == A)
    );

    // If X is HIGH, then A is HIGH and SLEEP is LOW.
    check_x_high_implies_a_high_and_sleep_low: assert property (
        @(posedge clk) (X == 1'b1) |-> (A == 1'b1 && SLEEP == 1'b0)
    );

    // If A is LOW, X must be LOW.
    check_a_low_forces_x_low: assert property (
        @(posedge clk) (A == 1'b0) |-> (X == 1'b0)
    );

    // If A is HIGH and SLEEP is LOW, X must be HIGH.
    check_awake_and_a_high_forces_x_high: assert property (
        @(posedge clk) (A == 1'b1 && SLEEP == 1'b0) |-> (X == 1'b1)
    );

    // If A and SLEEP are stable, X is stable.
    check_stable_inputs_imply_stable_output: assert property (
        @(posedge clk) ($stable(A) && $stable(SLEEP)) |-> $stable(X)
    );

    // X changes only if A or SLEEP changes.
    check_output_change_requires_input_change: assert property (
        @(posedge clk) $changed(X) |-> ($changed(A) || $changed(SLEEP))
    );

    // With SLEEP LOW in consecutive cycles, a rising A causes a rising X.
    check_a_rise_propagates_when_awake_stable: assert property (
        @(posedge clk) (SLEEP == 1'b0 && $past(SLEEP) == 1'b0 && $rose(A)) |-> $rose(X)
    );

    // With SLEEP LOW in consecutive cycles, a falling A causes a falling X.
    check_a_fall_propagates_when_awake_stable: assert property (
        @(posedge clk) (SLEEP == 1'b0 && $past(SLEEP) == 1'b0 && $fell(A)) |-> $fell(X)
    );

    // A rising SLEEP forces X LOW immediately.
    check_sleep_rise_forces_output_low: assert property (
        @(posedge clk) $rose(SLEEP) |-> (X == 1'b0)
    );

    // A falling SLEEP makes X equal to A immediately.
    check_sleep_fall_makes_output_follow_a: assert property (
        @(posedge clk) $fell(SLEEP) |-> (X == A)
    );
endmodule