module level_sensitive_buffer_isolation_cell_sva (
    input logic X,
    input logic A,
    input logic SLEEP,
    input logic VPWR
);

    // X must always match the implemented mux equation.
    check_output_matches_mux_equation: assert property (
        @($global_clock) disable iff (1'b0)
        X == (SLEEP ? A : 1'b0)
    );

    // When SLEEP is low, X must be forced low.
    check_output_forced_low_when_sleep_low: assert property (
        @($global_clock) disable iff (1'b0)
        !SLEEP |-> (X == 1'b0)
    );

    // When SLEEP is high, X must follow A.
    check_output_follows_a_when_sleep_high: assert property (
        @($global_clock) disable iff (1'b0)
        SLEEP |-> (X == A)
    );

    // A falling SLEEP transition must force X low.
    check_sleep_fall_forces_output_low: assert property (
        @($global_clock) disable iff (1'b0)
        !$initstate && $fell(SLEEP) |-> (X == 1'b0)
    );

    // A rising SLEEP transition must make X reflect A.
    check_sleep_rise_enables_data_path: assert property (
        @($global_clock) disable iff (1'b0)
        !$initstate && $rose(SLEEP) |-> (X == A)
    );

    // With SLEEP high and unchanged, a change on A must change X.
    check_a_change_propagates_when_sleep_high: assert property (
        @($global_clock) disable iff (1'b0)
        !$initstate && SLEEP && $stable(SLEEP) && $changed(A) |-> $changed(X)
    );

    // With SLEEP low and unchanged, a change on A must not affect X.
    check_a_change_blocked_when_sleep_low: assert property (
        @($global_clock) disable iff (1'b0)
        !$initstate && !SLEEP && $stable(SLEEP) && $changed(A) |-> (!$changed(X) && (X == 1'b0))
    );

    // If A and SLEEP are stable, X must remain stable.
    check_output_stable_when_inputs_stable: assert property (
        @($global_clock) disable iff (1'b0)
        !$initstate && $stable(A) && $stable(SLEEP) |-> $stable(X)
    );

endmodule