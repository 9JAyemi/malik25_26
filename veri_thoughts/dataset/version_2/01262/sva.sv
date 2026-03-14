module udp_dff_sva (
    input logic D,
    input logic CLK,
    input logic CLR,
    input logic SET,
    input logic Q,
    input logic QN
);
    // QN is always the complement of Q.
    check_qn_complement: assert property (
        @(posedge CLK) disable iff ($initstate) (QN == ~Q)
    );

    // CLR high at a clock drives Q low next cycle.
    check_clr_forces_zero: assert property (
        @(posedge CLK) disable iff ($initstate) CLR |=> (Q == 1'b0)
    );

    // SET high with CLR low drives Q high next cycle.
    check_set_forces_one_without_clear: assert property (
        @(posedge CLK) disable iff ($initstate) (!CLR && SET) |=> (Q == 1'b1)
    );

    // CLR has priority over SET when both are high.
    check_both_clr_set_prioritize_clear: assert property (
        @(posedge CLK) disable iff ($initstate) (CLR && SET) |=> (Q == 1'b0)
    );

    // With no control, Q follows D on the next cycle.
    check_no_ctrl_q_follows_d: assert property (
        @(posedge CLK) disable iff ($initstate) (!CLR && !SET) |=> (Q == $past(D))
    );

    // With no control, QN follows ~D on the next cycle.
    check_no_ctrl_qn_follows_not_d: assert property (
        @(posedge CLK) disable iff ($initstate) (!CLR && !SET) |=> (QN == ~$past(D))
    );

    // If no control and D equals current Q, Q holds value next cycle.
    check_hold_when_no_ctrl_and_D_eq_Q: assert property (
        @(posedge CLK) disable iff ($initstate) (!CLR && !SET && (D == Q)) |=> (Q == $past(Q))
    );

    // CLR high at a clock drives QN high next cycle.
    check_clr_sets_qn_high: assert property (
        @(posedge CLK) disable iff ($initstate) CLR |=> (QN == 1'b1)
    );

    // SET high with CLR low drives QN low next cycle.
    check_set_sets_qn_low_without_clear: assert property (
        @(posedge CLK) disable iff ($initstate) (!CLR && SET) |=> (QN == 1'b0)
    );

    // D rising with no control drives Q high next cycle.
    check_d_rise_drives_q_one: assert property (
        @(posedge CLK) disable iff ($initstate) (!CLR && !SET && $rose(D)) |=> (Q == 1'b1)
    );

    // D falling with no control drives Q low next cycle.
    check_d_fall_drives_q_zero: assert property (
        @(posedge CLK) disable iff ($initstate) (!CLR && !SET && $fell(D)) |=> (Q == 1'b0)
    );
endmodule