// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): sda_reg, falling_edge, rising_edge, cyc_cnt, start_cnt, time_cnt, start_bits, data_start, check_reset_state, assert, property, posedge, b000, d0, b0, b11, check_sda_shift_register, disable, iff, past, check_falling_edge_decode, b10, check_rising_edge_decode, b01, check_start_capture_update, d3, d1, b001, check_start_capture_hold, check_timer_idle_before_start, b111, check_preamble_timer_increment, d44500, check_preamble_done_sets_data_start, b1, check_bit_timer_increment, d11, d89000, check_bit_timer_wrap_advances_cycle, check_falling_edge_samples_one, d30000, d60000, h001, check_rising_edge_samples_zero, check_data_hold_without_sample_edge, check_status_matches_previous_data, b00011110101
bind ir_recieve ir_recieve_assertions auto_sva_inst (
    .clk(clk),
    .rst(rst),
    .sda(sda),
    .recieve_status(recieve_status),
    .recieved_data(recieved_data)
);
