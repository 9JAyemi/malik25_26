// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_reset_flush_outputs, assert, property, posedge, disable, iff, past, b0, h00, check_ack_flush_outputs, check_ready_blocked_by_prev_flush, check_ready_ack_clears_next, check_ready_fall_requires_prev_flush, fell, check_data_change_conditions, check_ready_sticky_without_prev_flush, check_data_stable_while_ready, check_no_ready_rise_after_prev_ack, rose, check_no_ready_rise_after_prev_reset
bind UART_Receiver UART_Receiver_sva auto_sva_inst (
    .Clk(Clk),
    .Reset(Reset),
    .Data(Data),
    .Ready(Ready),
    .Ack(Ack),
    .Rx(Rx)
);
