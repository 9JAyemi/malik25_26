module d_ffsr_sva (
    input logic CLK,
    input logic D,
    input logic S,
    input logic R,
    input logic Q,
    input logic QN
);
    ///// Synchronous set/reset and data load behavior /////
    // S asserted sets Q to 1 on the next clock (S has priority).
    check_sync_set_dominates: assert property (
        @(posedge CLK) disable iff (1'b0) (S == 1'b1) |=> (Q == 1'b1)
    );

    // R asserted with S deasserted clears Q to 0 on the next clock.
    check_sync_reset_when_no_set: assert property (
        @(posedge CLK) disable iff (1'b0) (S == 1'b0 && R == 1'b1) |=> (Q == 1'b0)
    );

    // When both S and R are asserted, S dominates and Q becomes 1 on the next clock.
    check_priority_s_over_r: assert property (
        @(posedge CLK) disable iff (1'b0) (S == 1'b1 && R == 1'b1) |=> (Q == 1'b1)
    );

    // With S=0 and R=0, Q loads D sampled at the same edge.
    check_data_load_when_no_ctrl: assert property (
        @(posedge CLK) disable iff (1'b0) ##1 ($past(S)==1'b0 && $past(R)==1'b0) |-> (Q == $past(D))
    );

    // If no control and D equals prior Q, Q holds its value across the next cycle.
    check_hold_when_d_equals_prev_q: assert property (
        @(posedge CLK) disable iff (1'b0) ##1 ($past(S)==1'b0 && $past(R)==1'b0 && ($past(D) == $past(Q))) |-> (Q == $past(Q))
    );

    // Any change in Q is justified by prior S/R/D values.
    check_q_change_has_cause: assert property (
        @(posedge CLK) disable iff (1'b0)
            ##1 $changed(Q) |-> (
                ($past(S) == 1'b1 && $past(Q) != 1'b1) ||
                ($past(S) == 1'b0 && $past(R) == 1'b1 && $past(Q) != 1'b0) ||
                ($past(S) == 1'b0 && $past(R) == 1'b0 && $past(D) != $past(Q))
            )
    );

    ///// Output relationship /////
    // QN is always the logical complement of Q.
    check_qn_is_complement_of_q: assert property (
        @(posedge CLK) disable iff (1'b0) (QN == ~Q)
    );

    // Q and QN are never equal.
    check_q_qn_never_equal: assert property (
        @(posedge CLK) disable iff (1'b0) (Q != QN)
    );

    // QN changes iff Q changes between consecutive clocks.
    check_qn_changes_iff_q_changes: assert property (
        @(posedge CLK) disable iff (1'b0) ##1 1'b1 |-> ($changed(QN) == $changed(Q))
    );

    ///// Functional summary check /////
    // Next Q equals: S?1 : (R?0 : D) using prior-cycle inputs.
    check_next_q_truth_table: assert property (
        @(posedge CLK) disable iff (1'b0)
            ##1 1'b1 |-> (Q == ($past(S) ? 1'b1 : ($past(R) ? 1'b0 : $past(D))))
    );
endmodule