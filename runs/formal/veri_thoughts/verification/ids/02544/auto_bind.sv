// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): State, StartBit, past, Idle, tRx, check_idle_to_startbit_half_count, assert, property, posedge, disable, iff, tReset, Count, N, b0, Full, check_startbit_abort_on_high_Rx, b1, check_startbit_to_receiving_on_low_Rx, Receiving, BitCount, d0, check_receiving_reload_count, check_receiving_shift, Temp, check_receiving_done_on_last_bit, NewData, Done, check_done_to_idle_on_high_tRx, check_data_latch_in_idle_when_newdata_no_ack, tAck, check_ready_rise_latches_data_and_clears_newdata, rose, check_count_decrements_when_nonzero, check_temp_changes_only_on_sample, changed
bind UART_Rx UART_Rx_sva auto_sva_inst (
    .Clk(Clk),
    .Rx(Rx),
    .Ready(Ready),
    .Data(Data)
);
