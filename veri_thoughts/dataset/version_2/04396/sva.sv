module frequency_counter_sva #(
    parameter int unsigned F_CLK = 40000,
    parameter int unsigned ERR = 5,
    parameter int unsigned NUM_CNTS_AVG = F_CLK/ERR
) (
    input logic        clk,
    input logic        sig,
    input logic [13:0] f,
    input logic [13:0] n_clk,
    input logic [9:0]  n_sig,
    input logic        reset
);

    // n_clk never counts past the averaging window.
    check_nclk_within_window: assert property (
        @(posedge clk) n_clk <= NUM_CNTS_AVG
    );

    // While counting, n_clk increments by one each clk.
    check_nclk_increments_while_counting: assert property (
        @(posedge clk) disable iff (reset)
        (n_clk < NUM_CNTS_AVG) |=> (n_clk == ($past(n_clk) + 14'd1))
    );

    // While counting, reset remains low.
    check_reset_low_while_counting: assert property (
        @(posedge clk) disable iff (reset)
        (n_clk < NUM_CNTS_AVG) |=> !reset
    );

    // While counting, f is not updated.
    check_f_stable_while_counting: assert property (
        @(posedge clk) disable iff (reset)
        (n_clk < NUM_CNTS_AVG) |=> (f == $past(f))
    );

    // Any non-reset clk sample has a positive in-range n_clk value.
    check_active_count_range: assert property (
        @(posedge clk)
        (!reset) |-> ((NUM_CNTS_AVG > 0) && (n_clk > 0) && (n_clk <= NUM_CNTS_AVG))
    );

    // n_clk is zero only during the reset pulse.
    check_zero_count_only_during_reset: assert property (
        @(posedge clk) (n_clk == 0) |-> reset
    );

    // Hitting the window limit raises reset and clears n_clk by the next clk.
    check_boundary_raises_reset_and_clears_nclk: assert property (
        @(posedge clk)
        (n_clk >= NUM_CNTS_AVG) |=> (reset && (n_clk == 0))
    );

    // Hitting the window limit clears n_sig by the next clk.
    check_boundary_clears_nsig: assert property (
        @(posedge clk)
        (n_clk >= NUM_CNTS_AVG) |=> (n_sig == 0)
    );

    // During reset, both counters are observed cleared.
    check_reset_clears_counters: assert property (
        @(posedge clk)
        reset |-> ((n_clk == 0) && (n_sig == 0))
    );

    // A reset pulse lasts one clk sample and restarts n_clk at 1.
    check_reset_pulse_restarts_count: assert property (
        @(posedge clk)
        (reset && (NUM_CNTS_AVG > 0)) |=> ((!reset) && (n_clk == 1))
    );

endmodule