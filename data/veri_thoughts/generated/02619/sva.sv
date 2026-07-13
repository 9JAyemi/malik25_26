module sky130_fd_sc_lp__sleep_pargate_plv_sva (
    input logic SLEEP,
    input logic VIRTPWR
);
    // No clock/reset in DUT; pure combinational logic
    // Behavior: VIRTPWR = ~SLEEP (active-high sleep forces power low)
    // Properties are sampled on edges of SLEEP/VIRTPWR

    // VIRTPWR must always be the inverse of SLEEP at any transition.
    check_virtpwr_complements_sleep: assert property (
        @(posedge SLEEP or negedge SLEEP or posedge VIRTPWR or negedge VIRTPWR)
        (VIRTPWR == ~SLEEP)
    );

    // When SLEEP rises, VIRTPWR must be LOW immediately.
    check_sleep_rise_forces_virtpwr_low: assert property (
        @(posedge SLEEP) (VIRTPWR == 1'b0)
    );

    // When SLEEP falls, VIRTPWR must be HIGH immediately.
    check_sleep_fall_forces_virtpwr_high: assert property (
        @(negedge SLEEP) (VIRTPWR == 1'b1)
    );

    // When VIRTPWR rises, SLEEP must be LOW.
    check_virtpwr_rise_implies_sleep_low: assert property (
        @(posedge VIRTPWR) (SLEEP == 1'b0)
    );

    // When VIRTPWR falls, SLEEP must be HIGH.
    check_virtpwr_fall_implies_sleep_high: assert property (
        @(negedge VIRTPWR) (SLEEP == 1'b1)
    );

    // SLEEP and VIRTPWR cannot both be HIGH.
    check_no_both_high: assert property (
        @(posedge SLEEP or negedge SLEEP or posedge VIRTPWR or negedge VIRTPWR)
        !(SLEEP && VIRTPWR)
    );

    // SLEEP and VIRTPWR cannot both be LOW.
    check_no_both_low: assert property (
        @(posedge SLEEP or negedge SLEEP or posedge VIRTPWR or negedge VIRTPWR)
        !((SLEEP == 1'b0) && (VIRTPWR == 1'b0))
    );

endmodule