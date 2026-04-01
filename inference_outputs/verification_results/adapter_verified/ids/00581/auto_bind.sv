// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_fifo_rdreq_only_on_timer800_nonempty, assert, property, posedge, disable, iff, pwm_timer, h800, check_fifo_rdreq_on_timer800_nonempty, b1, check_fifo_rdreq_deassert_on_timer801_after_request, past, h801, b0, check_fifo_rdreq_hold_on_timer801_no_request, check_sample_repeat_on_timerfff_after_load, data_rdy, hfff, audiodata_32, audiodata_32_p, check_sample_hold_on_timerfff_no_load, check_pwm_out_l_high_when_timer_le_left, check_pwm_out_l_low_when_timer_gt_left, check_pwm_out_r_high_when_timer_le_right, check_pwm_out_r_low_when_timer_gt_right
bind pwm_out pwm_out_sva auto_sva_inst (
    .clk(clk),
    .reset_n(reset_n),
    .fifo_rdreq(fifo_rdreq),
    .fifo_empty(fifo_empty),
    .fifo_data(fifo_data),
    .pwm_out_l(pwm_out_l),
    .pwm_out_r(pwm_out_r)
);
