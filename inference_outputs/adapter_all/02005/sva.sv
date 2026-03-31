module sky130_fd_sc_lp__iso0p_sva (
    input logic clk,
    input logic X,
    input logic A,
    input logic SLEEP
);

    // X must match the implemented AND/NOT function.
    check_iso_function: assert property (
        @(posedge clk) X == (A & ~SLEEP)
    );

    // When SLEEP is low, X must be high.
    check_sleep_low_forces_x_high: assert property (
        @(posedge clk) !SLEEP |-> X
    );

    // When SLEEP is high, X must be low.
    check_sleep_high_forces_x_low: assert property (
        @(posedge clk) SLEEP |-> !X
    );

    // A low forces X low.
    check_a_low_forces_x_low: assert property (
        @(posedge clk) !A |-> !X
    );

    // With SLEEP low and A high, X must be high.
    check_awake_and_a_high_sets_x: assert property (
        @(posedge clk) (!SLEEP && A) |-> X
    );

    // With SLEEP low and A low, X must be low.
    check_awake_and_a_low_clears_x: assert property (
        @(posedge clk) (!SLEEP && !A) |-> !X
    );

    // With SLEEP high and A high, X must be low.
    check_sleep_and_a_high_clears_x: assert property (
        @(posedge clk) (SLEEP && A) |-> !X
    );

    // With SLEEP high and A low, X must be low.
    check_sleep_and_a_low_clears_x: assert property (
        @(posedge clk) (SLEEP && !A) |-> !X
    );

endmodule