module TLU_sva (
    input logic EN,
    input logic SE,
    input logic CK,
    input logic Q
);
    // Q updates to SE on the next clock when EN is HIGH.
    check_update_on_en: assert property (
        @(posedge CK) EN |=> (Q == $past(SE))
    );

    // Q holds its value on the next clock when EN is LOW.
    check_hold_when_en_low: assert property (
        @(posedge CK) !EN |=> (Q == $past(Q))
    );

    // Any change in Q must be caused by EN being HIGH in the prior cycle.
    check_change_requires_en: assert property (
        @(posedge CK) (Q != $past(Q)) |-> $past(EN)
    );

    // When EN is HIGH and SE equals the prior Q, Q does not change.
    check_no_change_when_en_and_se_matches_prev_q: assert property (
        @(posedge CK) (EN && (SE == $past(Q))) |=> (Q == $past(Q))
    );

    // When EN is HIGH and SE differs from the prior Q, Q changes.
    check_change_when_en_and_se_differs_prev_q: assert property (
        @(posedge CK) (EN && (SE != $past(Q))) |=> (Q != $past(Q))
    );

    // If EN is HIGH and SE differs from the prior Q, Q must change to SE.
    check_update_to_se_when_en_and_se_differs_prev_q: assert property (
        @(posedge CK) (EN && (SE != $past(Q))) |=> (Q == $past(SE))
    );
endmodule