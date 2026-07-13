module sky130_fd_sc_lp__iso1p_sva (
    input logic X,
    input logic A,
    input logic SLEEP
);

    // X must implement A OR SLEEP.
    check_or_function: assert property (
        @($global_clock) X === (A | SLEEP)
    );

    // SLEEP high forces X high.
    check_sleep_high_forces_x_high: assert property (
        @($global_clock) (SLEEP === 1'b1) |-> (X === 1'b1)
    );

    // A high forces X high.
    check_a_high_forces_x_high: assert property (
        @($global_clock) (A === 1'b1) |-> (X === 1'b1)
    );

    // With SLEEP low, X follows A.
    check_sleep_low_passes_a: assert property (
        @($global_clock) (SLEEP === 1'b0) |-> (X === A)
    );

    // Both inputs low drive X low.
    check_both_low_drive_x_low: assert property (
        @($global_clock) ((A === 1'b0) && (SLEEP === 1'b0)) |-> (X === 1'b0)
    );

endmodule