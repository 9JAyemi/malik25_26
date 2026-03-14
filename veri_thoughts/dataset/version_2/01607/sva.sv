module dff_set_sva (
    input logic Q,
    input logic CLK,
    input logic D,
    input logic SET_B
);
    // Analysis:
    // - Clock: CLK (posedge)
    // - Async set: SET_B active-low; drives Q=1 when low
    // - Logic: sequential (DFF with asynchronous set)
    // - Behavior: if SET_B==0 -> Q=1 asynchronously; else on posedge CLK -> Q captures D

    ///// Asynchronous set behavior /////
    // When SET_B is LOW, Q must be driven HIGH.
    check_async_set_dominates: assert property (
        @(posedge CLK) (SET_B == 1'b0) |-> (Q == 1'b1)
    );

    // If SET_B is LOW across consecutive cycles, Q is HIGH in both.
    check_async_set_held_two_cycles: assert property (
        @(posedge CLK) (SET_B == 1'b0) && ($past(SET_B) == 1'b0) |-> (Q == 1'b1) && ($past(Q) == 1'b1)
    );

    ///// Synchronous capture when not set /////
    // With SET_B HIGH in both this and previous cycle, Q equals prior D.
    check_sync_capture_when_not_set: assert property (
        @(posedge CLK) disable iff (!SET_B) ($past(SET_B) == 1'b1) |-> (Q == $past(D))
    );

    // In normal mode, if D was stable over the last cycle, Q stays stable.
    check_stable_D_implies_stable_Q: assert property (
        @(posedge CLK) disable iff (!SET_B) ($past(SET_B) == 1'b1) && (D == $past(D)) |-> (Q == $past(Q))
    );

    // In normal mode, if Q changed this cycle, it must equal the prior D.
    check_Q_change_matches_prior_D: assert property (
        @(posedge CLK) disable iff (!SET_B) ($past(SET_B) == 1'b1) && (Q != $past(Q)) |-> (Q == $past(D))
    );

    // On the first clock after SET_B rises (release), Q captures D from the release edge.
    check_capture_after_set_release: assert property (
        @(posedge CLK) disable iff (!SET_B) $rose(SET_B) |-> ##1 (Q == $past(D,1))
    );

    ///// Sanity constraints derived from RTL /////
    // Q cannot be 0 while SET_B is LOW.
    check_Q_zero_implies_set_deasserted: assert property (
        @(posedge CLK) (Q == 1'b0) |-> (SET_B == 1'b1)
    );

    // A falling edge on Q implies prior D was 0 and SET_B was not asserted.
    check_Q_fall_origin: assert property (
        @(posedge CLK) $fell(Q) |-> ($past(SET_B) == 1'b1) && (SET_B == 1'b1) && ($past(D) == 1'b0)
    );

endmodule