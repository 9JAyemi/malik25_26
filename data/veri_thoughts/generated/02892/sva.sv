module TLATNTSCAX2TS_sva (
    input logic D,
    input logic E,
    input logic SE,
    input logic CK,
    input logic Q
);
    // On enable (E && SE), Q captures D (observed next cycle).
    capture_on_enable: assert property (
        @(posedge CK) disable iff ($initstate) (E && SE) |=> (Q == $past(D))
    );

    // When not enabled, Q holds its value to the next cycle.
    hold_when_disabled: assert property (
        @(posedge CK) disable iff ($initstate) !(E && SE) |=> (Q == $past(Q))
    );

    // Any change in Q must be caused by the enable being high in the previous cycle.
    change_requires_enable: assert property (
        @(posedge CK) disable iff ($initstate) (Q != $past(Q)) |-> $past(E && SE)
    );

    // When Q changes, it must take the previous cycle's D value.
    change_matches_prev_D: assert property (
        @(posedge CK) disable iff ($initstate) (Q != $past(Q)) |-> (Q == $past(D))
    );

    // If E is LOW, Q must hold to the next cycle.
    hold_when_E_low: assert property (
        @(posedge CK) disable iff ($initstate) !E |=> (Q == $past(Q))
    );

    // If SE is LOW, Q must hold to the next cycle.
    hold_when_SE_low: assert property (
        @(posedge CK) disable iff ($initstate) !SE |=> (Q == $past(Q))
    );

    // If enabled and D equals the current Q, Q remains unchanged next cycle.
    write_same_value_no_change: assert property (
        @(posedge CK) disable iff ($initstate) (E && SE && (D == $past(Q))) |=> (Q == $past(Q))
    );
endmodule