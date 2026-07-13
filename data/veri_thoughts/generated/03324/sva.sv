module sky130_fd_sc_hdll__inputiso0p_sva (
    input logic clk,
    input logic X,
    input logic A,
    input logic SLEEP
);

    wire sleepn;
    assign sleepn = ~SLEEP;

    // Output implements A gated by inverted SLEEP.
    check_iso_function: assert property (
        @(posedge clk) X == (A & sleepn)
    );

    // SLEEP high forces the output low.
    check_sleep_clamps_low: assert property (
        @(posedge clk) SLEEP |-> (X == 1'b0)
    );

    // When not asleep, the output follows A.
    check_awake_passes_input: assert property (
        @(posedge clk) sleepn |-> (X == A)
    );

    // A low forces the output low.
    check_low_input_clamps_low: assert property (
        @(posedge clk) !A |-> (X == 1'b0)
    );

    // A high and no sleep drives the output high.
    check_awake_high_input_drives_high: assert property (
        @(posedge clk) (A & sleepn) |-> (X == 1'b1)
    );

    // A high output requires A to be high.
    check_high_output_requires_high_input: assert property (
        @(posedge clk) X |-> A
    );

    // A high output requires SLEEP to be low.
    check_high_output_requires_not_sleep: assert property (
        @(posedge clk) X |-> sleepn
    );

endmodule