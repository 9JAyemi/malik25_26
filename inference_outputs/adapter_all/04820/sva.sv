module sky130_fd_sc_hd__lpflow_inputiso0n_sva (
    input logic clk,
    input logic X,
    input logic A,
    input logic SLEEP_B
);

    // X must equal the AND of A and SLEEP_B.
    check_x_matches_and: assert property (
        @(posedge clk) X == (A & SLEEP_B)
    );

    // When SLEEP_B is low, X must be low.
    check_sleep_low_forces_x_low: assert property (
        @(posedge clk) !SLEEP_B |-> !X
    );

    // When SLEEP_B is high, X must follow A.
    check_sleep_high_passes_a: assert property (
        @(posedge clk) SLEEP_B |-> (X == A)
    );

    // When A is low, X must be low.
    check_a_low_forces_x_low: assert property (
        @(posedge clk) !A |-> !X
    );

    // When A is high, X must follow SLEEP_B.
    check_a_high_passes_sleep: assert property (
        @(posedge clk) A |-> (X == SLEEP_B)
    );

    // X high requires both A and SLEEP_B high.
    check_x_high_requires_both_inputs: assert property (
        @(posedge clk) X |-> (A && SLEEP_B)
    );

endmodule