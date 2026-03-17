// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): reset_outputs_zero, assert, property, posedge, h0, b0, reset_release_clears_outputs, rose, outputs_known_when_active, disable, iff, isunknown, data_sign_single_cycle, b1, data_sign_no_back_to_back_rise, data_in_stable_when_sign_high, past, data_in_change_implies_sign_low, data_in_max_one_bit_change, onehot0, invalid_ctl_forces_sign_low_next, h6, h7, sign_rise_requires_prev_valid_ctl, prev_invalid_ctl_keeps_data_in_stable
bind my_uart_rx7to7 my_uart_rx7to7_sva auto_sva_inst (
    .clk(clk),
    .rst_n(rst_n),
    .uart_ctl(uart_ctl),
    .rs_rx(rs_rx),
    .data_in(data_in),
    .data_sign(data_sign)
);
