module sky130_fd_sc_lp__iso0p_sva (
    input logic X,
    input logic A,
    input logic SLEEP
);

    // X must equal A gated by the inverted SLEEP input.
    check_iso_function: assert property (
        @($global_clock) X == (A & ~SLEEP)
    );

    // When SLEEP is low, X must be high.
    check_awake_forces_high: assert property (
        @($global_clock) !SLEEP |-> X
    );

    // When SLEEP is high, X must match A.
    check_sleep_blocks_input: assert property (
        @($global_clock) SLEEP |-> (X == A)
    );

    // A low X can only occur when SLEEP is high and A is low.
    check_low_output_causes: assert property (
        @($global_clock) !X |-> (SLEEP && !A)
    );

endmodule