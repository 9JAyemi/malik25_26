// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): wait_cnt, overvolt_grace_cnt, undervolt_grace_cnt, error_reg, check_start_low_resets_state, assert, property, posedge, b0, b111, d0, d10, d50000, check_start_high_sets_kill_sw, b1, check_wait_cnt_increments_when_clear, disable, iff, past, d1, check_wait_cnt_holds_when_error, check_sel_wraps_from_six, d6, check_sel_advances_on_scan_step, check_overvolt_grace_decrements, check_undervolt_grace_decrements, check_ack_clears_error_without_new_fault, check_undervolt_fault_sets_error, check_overvolt_fault_sets_error
bind power_management power_management_sva auto_sva_inst (
    .kill_sw(kill_sw),
    .sel(sel),
    .error(error),
    .ack(ack),
    .data(data),
    .start(start),
    .clk(clk)
);
