module sky130_fd_sc_hd__lpflow_inputiso1n_sva (
    input logic X,
    input logic A,
    input logic SLEEP_B
);

    // X implements A OR inverted SLEEP_B.
    check_x_boolean_function: assert property (
        @($global_clock) X == (A | ~SLEEP_B)
    );

    // When SLEEP_B is low, isolation forces X high.
    check_sleep_low_forces_x_high: assert property (
        @($global_clock) (SLEEP_B == 1'b0) |-> (X == 1'b1)
    );

    // When SLEEP_B is high, X matches A.
    check_sleep_high_x_tracks_a: assert property (
        @($global_clock) (SLEEP_B == 1'b1) |-> (X == A)
    );

    // X can be low only when SLEEP_B is high and A is low.
    check_x_low_only_when_awake_and_a_low: assert property (
        @($global_clock) (X == 1'b0) |-> ((SLEEP_B == 1'b1) && (A == 1'b0))
    );

endmodule