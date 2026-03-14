module FFAR_sva (
    input logic Q,
    input logic C,
    input logic CE,
    input logic D,
    input logic R
);
    // Clock: C (posedge). No reset.
    // Behavior: Q updates to D on C when CE && R; otherwise Q holds.

    ///// Register next-state function /////
    // Next Q equals D when CE&&R last cycle, else holds previous Q.
    check_next_state_function: assert property (
        @(posedge C) disable iff ($initstate)
            Q == ( $past(CE && R) ? $past(D) : $past(Q) )
    );

    ///// Update behavior /////
    // When CE&&R was asserted, Q on this cycle equals D from last cycle.
    check_update_on_ce_r: assert property (
        @(posedge C) disable iff ($initstate)
            $past(CE && R) |-> (Q == $past(D))
    );

    ///// Hold behavior when CE low /////
    // If CE was LOW, Q must hold its previous value.
    check_hold_when_ce_low: assert property (
        @(posedge C) disable iff ($initstate)
            !$past(CE) |-> (Q == $past(Q))
    );

    ///// Hold behavior when R low under CE /////
    // If CE was HIGH and R was LOW, Q must hold.
    check_hold_when_r_low: assert property (
        @(posedge C) disable iff ($initstate)
            ($past(CE) && !$past(R)) |-> (Q == $past(Q))
    );

    ///// Change gating /////
    // Any change in Q must be due to CE&&R being HIGH last cycle.
    check_change_requires_enable: assert property (
        @(posedge C) disable iff ($initstate)
            (Q != $past(Q)) |-> $past(CE && R)
    );

    ///// Change value correctness /////
    // If Q changed, the new value must equal last cycle's D.
    check_change_matches_prev_D: assert property (
        @(posedge C) disable iff ($initstate)
            (Q != $past(Q)) |-> (Q == $past(D))
    );

    ///// Write of same data keeps Q unchanged /////
    // If CE&&R and D equaled prior Q, Q must not change.
    check_write_same_data_holds: assert property (
        @(posedge C) disable iff ($initstate)
            ($past(CE && R) && ($past(D) == $past(Q))) |-> (Q == $past(Q))
    );

    ///// Write of different data changes Q /////
    // If CE&&R and D differed from prior Q, Q must change.
    check_write_diff_data_changes: assert property (
        @(posedge C) disable iff ($initstate)
            ($past(CE && R) && ($past(D) != $past(Q))) |-> (Q != $past(Q))
    );

endmodule