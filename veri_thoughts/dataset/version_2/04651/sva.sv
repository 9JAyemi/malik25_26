module sky130_fd_sc_lp__inputiso0n_sva (
    input logic clk,
    input logic X,
    input logic A,
    input logic SLEEP_B
);

    // X must equal the AND of A and SLEEP_B.
    check_and_equivalence: assert property (
        @(posedge clk) X == (A & SLEEP_B)
    );

    // SLEEP_B low forces X low.
    check_sleep_forces_low: assert property (
        @(posedge clk) !SLEEP_B |-> !X
    );

    // When not sleeping, X must follow A.
    check_awake_passes_a: assert property (
        @(posedge clk) SLEEP_B |-> (X == A)
    );

    // A low forces X low.
    check_low_a_forces_low_output: assert property (
        @(posedge clk) !A |-> !X
    );

    // X high requires both A and SLEEP_B high.
    check_high_output_requires_both_inputs: assert property (
        @(posedge clk) X |-> (A & SLEEP_B)
    );

    // A and SLEEP_B high drives X high.
    check_both_inputs_high_drive_output_high: assert property (
        @(posedge clk) (A & SLEEP_B) |-> X
    );

endmodule