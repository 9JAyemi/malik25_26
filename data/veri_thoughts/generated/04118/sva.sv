module sky130_fd_sc_hdll__inputiso0p_sva (
    input logic X,
    input logic A,
    input logic SLEEP
);

    // Output matches the implemented gate function.
    check_output_matches_gate_function: assert property (
        @($global_clock) X == (A && !SLEEP)
    );

    // SLEEP high forces the output low.
    check_sleep_forces_output_low: assert property (
        @($global_clock) SLEEP |-> (X == 1'b0)
    );

    // With SLEEP low, the output follows A.
    check_awake_output_follows_input: assert property (
        @($global_clock) !SLEEP |-> (X == A)
    );

    // A low forces the output low.
    check_low_input_forces_output_low: assert property (
        @($global_clock) !A |-> (X == 1'b0)
    );

    // A high output requires A high and SLEEP low.
    check_high_output_requires_awake_high_input: assert property (
        @($global_clock) X |-> (A == 1'b1 && SLEEP == 1'b0)
    );

endmodule