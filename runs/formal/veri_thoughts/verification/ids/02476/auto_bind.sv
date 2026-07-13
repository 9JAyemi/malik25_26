// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_reset_idle_gnt0, assert, property, b0, check_first_cycle_after_reset_idle, disable, iff, rose, check_state_trans_from_idle, past, check_state_trans_from_bbusy, check_state_trans_from_bwait, check_state_trans_from_bfree, check_gnt_definition, check_gnt_low_in_idle, check_gnt_low_in_bfree, check_gnt_rise_targets_busy_or_wait, check_gnt_fall_targets_idle_or_free, fell
bind bus_fsm bus_fsm_sva auto_sva_inst (
    .gnt(gnt),
    .state(state),
    .dly(dly),
    .done(done),
    .req(req),
    .clk(clk),
    .rst_n(rst_n),
    .IDLE(IDLE),
    .b00(b00),
    .BBUSY(BBUSY),
    .b01(b01),
    .BWAIT(BWAIT),
    .b10(b10),
    .BFREE(BFREE),
    .b11(b11),
    .posedge(posedge)
);
