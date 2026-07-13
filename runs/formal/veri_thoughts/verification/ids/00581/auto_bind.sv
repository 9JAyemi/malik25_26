// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): data_rdy, pwm_timer, audiodata_32, audiodata_32_p, check_reset_regs_zero, assert, property, posedge, d0, b0, check_reset_pwm_out_high, b1, check_timer_increments, disable, iff, past, d1, check_rdreq_set_at_800, h800, check_rdreq_high_only_at_801, h801, check_rdreq_rise_requires_not_empty_800, rose, check_rdreq_clear_after_801, check_rdreq_one_cycle_pulse, check_capture_data_on_801, check_data_rdy_set_after_801, check_data_rdy_holds_until_fff, hfff, check_data_rdy_clear_at_fff, check_audiodata32_update_at_fff, check_audiodata32_changes_only_on_fff, changed, check_audiodata32p_changes_only_on_801, check_pwm_out_l_high_when_lte, check_pwm_out_l_low_when_gt, check_pwm_out_r_high_when_lte, check_pwm_out_r_low_when_gt, check_pwm_out_l_known_when_inputs_known, isunknown, check_pwm_out_r_known_when_inputs_known, check_pwms_equal_when_thresholds_equal
bind pwm_out pwm_out_sva auto_sva_inst (
    .clk(clk),
    .reset_n(reset_n),
    .fifo_rdreq(fifo_rdreq),
    .fifo_empty(fifo_empty),
    .fifo_data(fifo_data),
    .pwm_out_l(pwm_out_l),
    .pwm_out_r(pwm_out_r)
);
