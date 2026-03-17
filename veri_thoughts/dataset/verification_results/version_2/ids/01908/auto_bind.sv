// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): reset_led_status_zero, assert, property, h00, reset_switch_path_zero, led_updates_on_we_ffff, disable, iff, past, led_holds_without_enable, led_change_requires_prev_enable, dataout_switch_samples_prev, dataout_mem_write_same_cycle, dataout_mem_hold_no_write, led_zero_after_reset_until_write
bind sram memory_decoder_sva auto_sva_inst (
    .address(address),
    .data_in(data_in),
    .switch_in(switch_in),
    .clk(clk),
    .res(res),
    .write_enable(write_enable),
    .LED_status(LED_status),
    .data_out(data_out),
    .posedge(posedge)
);
