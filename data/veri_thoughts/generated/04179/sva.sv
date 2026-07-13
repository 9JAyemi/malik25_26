module sky130_fd_sc_hdll__isobufsrc_sva (
    input logic A,
    input logic Z,
    input logic SLEEP
);

    // When sleep is asserted, the output is forced low.
    check_sleep_forces_low: assert property (
        @($global_clock) (SLEEP |-> (Z == 1'b0))
    );

    // When sleep is deasserted, the output follows A.
    check_awake_passes_input: assert property (
        @($global_clock) (!SLEEP |-> (Z == A))
    );

    // The observable output matches the implemented function.
    check_output_function: assert property (
        @($global_clock) (Z == (SLEEP ? 1'b0 : A))
    );

endmodule