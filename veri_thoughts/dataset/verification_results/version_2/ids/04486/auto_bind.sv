// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_reset_state, assert, property, b0, check_sync_stage_lsb_capture, disable, iff, past, check_sync_stage_msb_capture, check_counter_clears_on_match, check_counter_increments_on_mismatch, h00001, check_counter_wraps_after_terminal_count, check_output_toggles_on_terminal_count, check_output_holds_without_terminal_count, check_output_change_requires_terminal_count
bind sync_debouncer_10ms sync_debouncer_10ms_sva auto_sva_inst (
    .signal_debounced(signal_debounced),
    .clk_50mhz(clk_50mhz),
    .rst(rst),
    .signal_async(signal_async),
    .sync_stage(sync_stage),
    .debounce_counter(debounce_counter),
    .signal_sync(signal_sync),
    .debounce_counter_done(debounce_counter_done),
    .h7ffff(h7ffff),
    .posedge(posedge),
    .b00(b00),
    .h00000(h00000)
);
