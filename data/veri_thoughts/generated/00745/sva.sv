module d_ff_en_sva (
    input logic CLK,
    input logic D,
    input logic EN,
    input logic Q
);
    // Next state of Q equals mux of previous EN: EN?D_prev:Q_prev.
    check_next_value_mux: assert property (
        @(posedge CLK) 1'b1 |-> ##1 (Q == ($past(EN) ? $past(D) : $past(Q)))
    );

    // When EN is high, Q updates to previous D on next clock.
    check_update_on_en: assert property (
        @(posedge CLK) EN |-> ##1 (Q == $past(D))
    );

    // When EN is low, Q holds its previous value on next clock.
    check_hold_when_not_en: assert property (
        @(posedge CLK) !EN |-> ##1 (Q == $past(Q))
    );

    // Any change in Q between cycles must be caused by EN being high in the prior cycle.
    check_change_requires_enable: assert property (
        @(posedge CLK) 1'b1 |-> ##1 ((Q != $past(Q)) |-> $past(EN))
    );

    // If EN is high and D equals current Q, Q does not change next cycle.
    check_en_same_value_no_change: assert property (
        @(posedge CLK) (EN && (D == Q)) |-> ##1 (Q == $past(Q))
    );

    // If EN is high and D differs from current Q, Q changes next cycle.
    check_en_diff_value_change: assert property (
        @(posedge CLK) (EN && (D != Q)) |-> ##1 (Q != $past(Q))
    );

    // If EN was high and Q changed, the new Q equals the previous D.
    check_change_matches_prev_d_when_en: assert property (
        @(posedge CLK) 1'b1 |-> ##1 (( $past(EN) && (Q != $past(Q)) ) |-> (Q == $past(D)))
    );

    // If EN was low and D differed from Q, Q must not equal previous D on next cycle.
    check_blocked_update_when_en_low: assert property (
        @(posedge CLK) 1'b1 |-> ##1 (( !$past(EN) && ($past(D) != $past(Q)) ) |-> (Q != $past(D)))
    );
endmodule