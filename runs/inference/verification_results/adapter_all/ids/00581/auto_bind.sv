// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): data_rdy, pwm_timer, audiodata_32, audiodata_32_p, check_reset_clears_state, assert, property, posedge, d0, b0, check_pwm_timer_increments, disable, iff, b1, past, d1, check_fifo_rdreq_on_sample, h800, check_fifo_rdreq_clears_on_sample, h801, check_audiodata_p_captures_on_sample, check_data_rdy_sets_on_sample, check_audiodata_loads_on_hold, hfff, check_data_rdy_clears_on_hold, check_pwm_out_l_compare, bx, check_pwm_out_r_compare
bind pwm_out pwm_out_sva auto_sva_inst (
    .clk(clk),
    .reset_n(reset_n),
    .fifo_rdreq(fifo_rdreq),
    .fifo_empty(fifo_empty),
    .fifo_data(fifo_data),
    .pwm_out_l(pwm_out_l),
    .pwm_out_r(pwm_out_r)
);
