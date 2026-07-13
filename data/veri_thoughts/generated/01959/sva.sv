module d_ff_en_sva (
    input logic D,
    input logic EN,
    input logic CLK,
    input logic Q
);
    ///// Functional next-state behavior /////
    // Next cycle Q equals (EN ? D : Q) from the previous cycle.
    check_next_state_equation: assert property (
        @(posedge CLK) 1'b1 |=> (Q == ($past(EN) ? $past(D) : $past(Q)))
    );

    ///// Update behavior /////
    // When EN is 1, Q on the next cycle equals D from this cycle.
    check_update_on_enable: assert property (
        @(posedge CLK) EN |=> (Q == $past(D))
    );

    // When EN is 0, Q holds its previous value.
    check_hold_on_disable: assert property (
        @(posedge CLK) !EN |=> (Q == $past(Q))
    );

    ///// Change conditions /////
    // Any change in Q must be caused by EN being 1 in the previous cycle.
    check_q_change_implies_prev_enable: assert property (
        @(posedge CLK) $changed(Q) |-> $past(EN)
    );

    // If EN=1 and D equals prior Q, Q does not change next cycle.
    check_no_change_when_assigning_same_value: assert property (
        @(posedge CLK) EN && (D == $past(Q)) |=> (Q == $past(Q))
    );

    // If EN=1 and D differs from prior Q, Q changes next cycle.
    check_change_when_enabled_and_data_differs: assert property (
        @(posedge CLK) EN && (D != $past(Q)) |=> (Q != $past(Q))
    );

    ///// Multi-cycle consistency /////
    // If EN=0 for two consecutive cycles, Q two cycles later equals its value two cycles ago.
    check_two_cycle_hold_when_disabled: assert property (
        @(posedge CLK) !EN ##1 !EN |=> (Q == $past(Q,2))
    );

    // If EN=1 for two consecutive cycles, Q two cycles later equals D from one cycle ago.
    check_two_cycle_enable_latest_data: assert property (
        @(posedge CLK) EN ##1 EN |=> (Q == $past(D,1))
    );

endmodule