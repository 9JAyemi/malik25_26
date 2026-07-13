// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): fifo_read_request, assert, property, posedge, disable, iff, fifo_read_request_deassert, pwm_timer_increment, pwm_timer, b1, pwm_timer_reset, pwm_out_l_check, pwm_out_l_check_2, b0, pwm_out_r_check, pwm_out_r_check_2, audio_data_update, data_rdy, audiodata_32, audiodata_32_p, data_ready_clear
bind pwm_out pwm_out_sva auto_sva_inst (
    .clk(clk),
    .reset_n(reset_n),
    .fifo_rdreq(fifo_rdreq),
    .fifo_empty(fifo_empty),
    .fifo_data(fifo_data),
    .pwm_out_l(pwm_out_l),
    .pwm_out_r(pwm_out_r)
);
