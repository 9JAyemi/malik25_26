module dff_preset_clear_sva (
    input logic Q,
    input logic D,
    input logic C,
    input logic R,
    input logic P
);
    // On posedge C, R=1 clears Q on the next clock.
    check_sync_clear: assert property (
        @(posedge C) disable iff (1'b0) R |=> (Q == 1'b0)
    );

    // On posedge C, with R=0 and P=1, Q is set to 1 on the next clock.
    check_sync_preset: assert property (
        @(posedge C) disable iff (1'b0) (!R && P) |=> (Q == 1'b1)
    );

    // On posedge C, with R=0 and P=0, Q captures D on the next clock.
    check_data_capture: assert property (
        @(posedge C) disable iff (1'b0) (!R && !P) |=> (Q == $past(D))
    );

    // If both R and P are 1, clear has priority and Q becomes 0 on the next clock.
    check_clear_priority_over_preset: assert property (
        @(posedge C) disable iff (1'b0) (R && P) |=> (Q == 1'b0)
    );

    // Next-state equation: Q equals previous cycle's muxed result of R/P/D.
    check_next_state_function: assert property (
        @(posedge C) disable iff (1'b0)
            $past(1'b1) |-> ( Q == ( $past(R) ? 1'b0 : ( $past(P) ? 1'b1 : $past(D) ) ) )
    );

    // With R=0,P=0 and D=1 at a clock, Q becomes 1 on the next clock.
    check_data1_capture: assert property (
        @(posedge C) disable iff (1'b0) (!R && !P && D) |=> (Q == 1'b1)
    );

    // With R=0,P=0 and D=0 at a clock, Q becomes 0 on the next clock.
    check_data0_capture: assert property (
        @(posedge C) disable iff (1'b0) (!R && !P && !D) |=> (Q == 1'b0)
    );

    // If previously R=0,P=0 and D==Qprev, Q holds its value now.
    check_hold_when_data_matches_prev: assert property (
        @(posedge C) disable iff (1'b0)
            ($past(1'b1) && !$past(R) && !$past(P) && ($past(D) == $past(Q))) |-> (Q == $past(Q))
    );

    // If previously R=0,P=0 and D!=Qprev, Q toggles relative to Qprev now.
    check_toggle_when_data_differs_prev: assert property (
        @(posedge C) disable iff (1'b0)
            ($past(1'b1) && !$past(R) && !$past(P) && ($past(D) != $past(Q))) |-> (Q != $past(Q))
    );

    // If previously P=1 and R=0, Q is 1 now.
    check_prev_preset_sets_q: assert property (
        @(posedge C) disable iff (1'b0)
            ($past(1'b1) && !$past(R) && $past(P)) |-> (Q == 1'b1)
    );
endmodule