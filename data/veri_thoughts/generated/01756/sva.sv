module d_flip_flop_async_reset_sva (
    input logic CLK,
    input logic RESET_B, // active-low async reset
    input logic D,
    input logic Q
);

    ///// Reset behavior /////
    // While reset is asserted low, Q must be 0.
    check_reset_low_forces_zero: assert property (
        @(posedge CLK) (!RESET_B) |-> (Q == 1'b0)
    );

    // When reset falls (1->0), Q is 0 at this sample.
    check_reset_fall_clears_q: assert property (
        @(posedge CLK) $fell(RESET_B) |-> (Q == 1'b0)
    );

    // If reset is low in consecutive cycles, Q remains 0 across them.
    check_reset_hold_zero: assert property (
        @(posedge CLK) (!$past(RESET_B) && !RESET_B) |-> ($past(Q) == 1'b0 && Q == 1'b0)
    );

    ///// Normal capture behavior /////
    // With reset high now and previously, Q equals previous D.
    check_capture_prev_d_when_reset_high: assert property (
        @(posedge CLK) disable iff (!RESET_B) $past(RESET_B) |-> (Q == $past(D))
    );

    // After reset deasserts (prev low, now high), next cycle Q equals D from deassert cycle.
    check_capture_after_reset_release: assert property (
        @(posedge CLK) disable iff (!RESET_B) (!$past(RESET_B) && RESET_B) |=> (Q == $past(D))
    );

    // If reset high for last two cycles and D did not change, Q does not change.
    check_q_stable_if_prev_two_d_equal: assert property (
        @(posedge CLK) disable iff (!RESET_B)
            ($past(RESET_B) && $past(RESET_B,2) && ($past(D) == $past(D,2))) |-> (Q == $past(Q))
    );

    // If reset high for last two cycles and D changed, Q must change.
    check_q_changes_if_prev_two_d_differ: assert property (
        @(posedge CLK) disable iff (!RESET_B)
            ($past(RESET_B) && $past(RESET_B,2) && ($past(D) != $past(D,2))) |-> (Q != $past(Q))
    );

    // If reset high for last two cycles and Q changed, D must have changed in prior cycle.
    check_q_change_implies_prev_d_change: assert property (
        @(posedge CLK) disable iff (!RESET_B)
            ($past(RESET_B) && $past(RESET_B,2) && (Q != $past(Q))) |-> ($past(D) != $past(D,2))
    );

endmodule