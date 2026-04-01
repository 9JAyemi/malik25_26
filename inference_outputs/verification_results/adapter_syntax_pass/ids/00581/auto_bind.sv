// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): data_rdy, pwm_timer, audiodata_32, audiodata_32_p, check_reset_state, assert, property, posedge, d0, b0, check_pwm_timer_increment, disable, iff, b1, past, d1, check_fifo_rdreq_on_800, h800, check_fifo_rdreq_on_801, h801, check_fifo_rdreq_on_fff, hFFF, check_fifo_rdreq_only_on_800, check_data_rdy_on_801, check_data_rdy_on_fff, check_data_rdy_only_on_801, check_audiodata_p_capture, check_audiodata_load, check_pwm_out_l_low_nibble, check_pwm_out_l_high_nibble, check_pwm_out_r_high_nibble, check_pwm_out_r_low_nibble
bind pwm_out pwm_out_sva auto_sva_inst (
    .clk(clk),
    .reset_n(reset_n),
    .fifo_rdreq(fifo_rdreq),
    .fifo_empty(fifo_empty),
    .fifo_data(fifo_data),
    .pwm_out_l(pwm_out_l),
    .pwm_out_r(pwm_out_r)
);
