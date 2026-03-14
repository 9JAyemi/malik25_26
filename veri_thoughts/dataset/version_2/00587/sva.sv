module synchronizer_ff_sva (
    input logic [3:0] D,
    input logic [3:0] Q,
    input logic m_aclk,
    input logic AR
);
    ///// Reset behavior /////
    // While reset is asserted (AR=0), D must be 0.
    check_reset_forces_zero: assert property (
        @(posedge m_aclk) (!AR) |-> (D == 4'b0000)
    );
    // On reset assertion, D is 0 at this clock.
    check_reset_assert_cycle_zero: assert property (
        @(posedge m_aclk) $fell(AR) |-> (D == 4'b0000)
    );
    // On reset deassertion, D remains 0 at this clock (pre-NBA sample).
    check_reset_deassert_cycle_zero: assert property (
        @(posedge m_aclk) $rose(AR) |-> (D == 4'b0000)
    );

    ///// Normal operation /////
    // With AR high for two consecutive clocks, D equals Q from the previous clock.
    check_capture_latency: assert property (
        @(posedge m_aclk) disable iff (!AR) $past(AR) |-> (D == $past(Q))
    );
    // After reset deasserts, on the next clock D equals Q sampled at deassertion.
    check_capture_after_reset_release: assert property (
        @(posedge m_aclk) disable iff (!AR) $rose(AR) |-> ##1 (AR && (D == $past(Q)))
    );
    // If Q is stable across clocks while out of reset, D remains stable.
    check_stable_Q_keeps_D_stable: assert property (
        @(posedge m_aclk) disable iff (!AR) ($past(AR) && (Q == $past(Q))) |-> (D == $past(D))
    );
    // If D changes (and AR was high for the last two clocks), then prior-Q changed.
    check_D_change_has_prior_Q_change: assert property (
        @(posedge m_aclk) disable iff (!AR) ($past(AR) && $past($past(AR)) && (D != $past(D))) |-> ($past(Q) != $past($past(Q)))
    );
    // If prior-Q changed (and AR was high for the last two clocks), then D changes.
    check_Q_change_causes_D_change: assert property (
        @(posedge m_aclk) disable iff (!AR) ($past(AR) && $past($past(AR)) && ($past(Q) != $past($past(Q)))) |-> (D != $past(D))
    );
endmodule