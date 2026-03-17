// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_qn_is_inversion_of_q, assert, property, check_set_dominates_clr, check_set_forces_q_high, check_clr_forces_q_low_when_no_set, check_clr_sets_qn_high_when_no_set, check_d_captured_into_q_on_next_clk, past, check_d_captured_into_qn_on_next_clk, check_full_next_state_q, check_hold_when_d_equals_q
bind d_ff_as top_module_sva auto_sva_inst (
    .CLK(CLK),
    .D(D),
    .SET(SET),
    .CLR(CLR),
    .Q(Q),
    .Q_N(Q_N),
    .posedge(posedge),
    .b1(b1),
    .b0(b0)
);
