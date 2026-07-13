// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): ttyclk, ttyclk_bit, ttyclk_start, shift_in, count, rxd, rxd2, check_input_synchronizer, assert, property, posedge, b1, past, check_ttyclk_countdown, d1, check_bit_sample_nonfinal, check_bit_sample_final, d0, check_start_bit_detect, d8, check_idle_hold, check_attention_update, check_received_data_update
bind rs232in rs232in_sva auto_sva_inst (
    .clock(clock),
    .serial_in(serial_in),
    .attention(attention),
    .received_data(received_data)
);
