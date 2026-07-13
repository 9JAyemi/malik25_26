module myDFF_sva (
    input logic CK,
    input logic D,
    input logic RN,   // Active-HIGH synchronous reset
    input logic SN,   // Active-HIGH synchronous set
    input logic Q,
    input logic QN
);

    ///// Synchronous control behavior /////
    // When RN is asserted at a clock edge, Q must be 0 on the next cycle.
    check_sync_reset_drives_q0: assert property (
        @(posedge CK) RN |=> (Q == 1'b0)
    );

    // When SN is asserted (and RN is not), Q must be 1 on the next cycle.
    check_sync_set_drives_q1: assert property (
        @(posedge CK) disable iff (RN) SN |=> (Q == 1'b1)
    );

    // When neither RN nor SN is asserted, Q captures D on the next cycle.
    check_data_capture_when_no_ctrl: assert property (
        @(posedge CK) disable iff (RN) (!SN) |=> (Q == $past(D))
    );

    // RN has priority over SN when both are asserted; Q must be 0 next cycle.
    check_reset_priority_over_set: assert property (
        @(posedge CK) (RN && SN) |=> (Q == 1'b0)
    );

    ///// Complementary output /////
    // QN is always the bitwise complement of Q.
    check_qn_complements_q: assert property (
        @(posedge CK) (QN == ~Q)
    );

    // When neither RN nor SN is asserted, QN next equals inversion of current D.
    check_qn_reflects_d_on_data_capture: assert property (
        @(posedge CK) disable iff (RN) (!SN) |=> (QN == ~$past(D))
    );

    // When SN is asserted (and RN is not), QN must be 0 on the next cycle.
    check_qn_zero_on_set: assert property (
        @(posedge CK) disable iff (RN) SN |=> (QN == 1'b0)
    );

    // When RN is asserted, QN must be 1 on the next cycle.
    check_qn_one_on_reset: assert property (
        @(posedge CK) RN |=> (QN == 1'b1)
    );

endmodule