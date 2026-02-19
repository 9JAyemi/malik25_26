module myDFF_sva (
    input logic CK,
    input logic D,
    input logic RN,
    input logic SN,
    input logic Q,
    input logic QN
);

    /*
    Analysis summary for myDFF:
    - Clock: CK (posedge)
    - Resets/sets (synchronous, active-high):
        * RN: synchronous reset-to-0 with highest priority
        * SN: synchronous set-to-1 with lower priority than RN
    - Logic type: Sequential flip-flop with synchronous control; QN is purely combinational as ~Q
    - Behavior on posedge CK:
        * if (RN)        Q <= 0;
        * else if (SN)   Q <= 1;
        * else           Q <= D;
      Continuous assignment: QN = ~Q

    Note: There is no asynchronous reset in this RTL. Assertions below are clocked on posedge CK.
    For consistency with the style guideline, disable iff(1'b0) is used to indicate no async reset gating.
    */

    ///// Core functional mapping from previous cycle to current Q /////
    // When RN was asserted in the previous cycle, Q must be 0 in the current cycle.
    check_rn_forces_zero_next: assert property (
        @(posedge CK) disable iff (1'b0)
            $past(RN) |-> (Q == 1'b0)
    );

    // When SN was asserted (and RN was deasserted) in the previous cycle, Q must be 1 in the current cycle.
    check_sn_sets_one_next: assert property (
        @(posedge CK) disable iff (1'b0)
            ($past(SN) && !$past(RN)) |-> (Q == 1'b1)
    );

    // When neither RN nor SN was asserted in the previous cycle, Q must capture D from the previous cycle.
    check_data_captured_when_no_ctrl: assert property (
        @(posedge CK) disable iff (1'b0)
            (!$past(RN) && !$past(SN)) |-> (Q == $past(D))
    );

    // If both RN and SN were asserted in the previous cycle, RN has priority and forces Q to 0.
    check_rn_priority_over_sn: assert property (
        @(posedge CK) disable iff (1'b0)
            ($past(RN) && $past(SN)) |-> (Q == 1'b0)
    );

    ///// Complementary output /////
    // QN is always the bitwise inversion of Q (continuous assign).
    check_qn_is_complement: assert property (
        @(posedge CK) disable iff (1'b0)
            (QN == ~Q)
    );

    // Whenever Q changes between cycles, QN must change as well (since QN == ~Q).
    check_qn_changes_with_q: assert property (
        @(posedge CK) disable iff (1'b0)
            $changed(Q) |-> ($changed(QN) && (QN == ~Q))
    );

    // If Q does not change between cycles, QN must also remain unchanged.
    check_qn_stable_when_q_stable: assert property (
        @(posedge CK) disable iff (1'b0)
            !$changed(Q) |-> !$changed(QN)
    );

    ///// Useful corollaries (follow from core mapping) /////
    // If RN was asserted in the previous cycle, QN must be 1 in the current cycle (since Q is 0).
    check_qn_after_rn_prev: assert property (
        @(posedge CK) disable iff (1'b0)
            $past(RN) |-> (QN == 1'b1)
    );

    // If SN was asserted (and RN deasserted) in the previous cycle, QN must be 0 in the current cycle (since Q is 1).
    check_qn_after_sn_prev: assert property (
        @(posedge CK) disable iff (1'b0)
            ($past(SN) && !$past(RN)) |-> (QN == 1'b0)
    );

    // If neither RN nor SN was asserted in the previous cycle and D matched Q in the previous cycle,
    // then Q remains unchanged in the current cycle (stability corollary of data capture).
    check_q_stability_when_data_matches_prev: assert property (
        @(posedge CK) disable iff (1'b0)
            (!$past(RN) && !$past(SN) && ($past(D) == $past(Q))) |-> (Q == $past(Q))
    );

endmodule