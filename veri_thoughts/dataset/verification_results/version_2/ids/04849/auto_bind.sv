// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): trn_pending, check_trn_pending_reset, assert, property, posedge, b0, check_cfg_turnoff_ok_reset, check_trn_pending_set_on_request, disable, iff, b1, check_trn_pending_stays_low_without_request, check_trn_pending_clear_on_completion, check_trn_pending_hold_while_waiting, check_turnoff_ok_when_requested_and_idle, check_turnoff_ok_low_without_request, check_turnoff_ok_blocked_by_pending
bind PIO_TO_CTRL PIO_TO_CTRL_sva auto_sva_inst (
    .clk(clk),
    .rst_n(rst_n),
    .req_compl_i(req_compl_i),
    .compl_done_i(compl_done_i),
    .cfg_to_turnoff(cfg_to_turnoff),
    .cfg_turnoff_ok(cfg_turnoff_ok)
);
