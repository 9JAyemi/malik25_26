module sky130_fd_sc_hd__lpflow_inputiso0n_sva (
    input logic X,
    input logic A,
    input logic SLEEP_B
);

    // Output implements the AND of A and SLEEP_B.
    check_output_and_function: assert property (
        @($global_clock) X == (A & SLEEP_B)
    );

    // Low SLEEP_B forces the output low.
    check_sleep_forces_zero: assert property (
        @($global_clock) !SLEEP_B |-> !X
    );

    // Low A forces the output low.
    check_a_forces_zero_when_low: assert property (
        @($global_clock) !A |-> !X
    );

    // With SLEEP_B high, the output follows A.
    check_output_follows_a_when_awake: assert property (
        @($global_clock) SLEEP_B |-> (X == A)
    );

    // A high output requires both inputs to be high.
    check_output_high_requires_both_inputs: assert property (
        @($global_clock) X |-> (A && SLEEP_B)
    );

endmodule