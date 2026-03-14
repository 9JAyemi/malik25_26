module sync_reset_DFF_sva (
    input logic D,
    input logic GSR,   // synchronous active-high reset
    input logic CLK,
    input logic Q
);
    // If reset was asserted on the previous cycle, Q is 0 now.
    check_sync_reset_clears_q: assert property (
        @(posedge CLK) $past(GSR) |-> (Q == 1'b0)
    );

    // When not in reset on the previous cycle, Q reflects D from the previous cycle.
    check_data_captured_when_no_reset: assert property (
        @(posedge CLK) disable iff (GSR) $past(!GSR) |-> (Q == $past(D))
    );

    // On a cycle where reset just deasserted, Q remains 0 (held from prior reset capture).
    check_q_zero_on_reset_deassert_cycle: assert property (
        @(posedge CLK) $fell(GSR) |-> (Q == 1'b0)
    );

    // While reset is held across consecutive cycles, Q stays 0.
    check_q_held_low_while_reset_high: assert property (
        @(posedge CLK) ($past(GSR) && GSR) |-> (Q == 1'b0)
    );

    // If not in reset for two consecutive cycles, Q's transition matches D's prior transition.
    check_q_transition_matches_d_transition_no_reset: assert property (
        @(posedge CLK) disable iff (GSR) (!$past(GSR) && !$past($past(GSR))) |-> ((Q ^ $past(Q)) == ($past(D) ^ $past($past(D))))
    );

    // If not in reset for two consecutive cycles and D was stable, Q is stable.
    check_q_holds_when_d_stable_no_reset: assert property (
        @(posedge CLK) disable iff (GSR) (!$past(GSR) && !$past($past(GSR)) && ($past(D) == $past($past(D)))) |-> (Q == $past(Q))
    );
endmodule