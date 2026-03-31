// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_busy_decode, assert, property, check_tx_decode, check_start_load_shift, past, check_start_moves_to_start_state, check_idle_holds_without_start, check_start_state_to_data0, check_active_holds_without_bittick, check_data_states_increment_on_tick, b0001, check_last_data_to_stop1, check_stop1_to_stop2, check_stop2_to_idle, check_shift_right_on_data_tick, check_shift_stable_without_load_or_shift, stable, check_default_state_recovers_on_tick, b0101, b0110, b0111
bind RS232TX RS232TX_sva auto_sva_inst (
    .clk(clk),
    .Tx_start(Tx_start),
    .dbuffer(dbuffer),
    .Tx(Tx),
    .Tx_busy(Tx_busy),
    .bittick(bittick),
    .Tx_state(Tx_state),
    .Tx_shift(Tx_shift),
    .posedge(posedge),
    .b0000(b0000),
    .b0100(b0100),
    .b1000(b1000),
    .b1111(b1111),
    .b0010(b0010),
    .b0011(b0011)
);
