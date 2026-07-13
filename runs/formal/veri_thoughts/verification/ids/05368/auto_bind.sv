// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_reset_release_clears_serial, assert, property, posedge, disable, iff, fell, b0, check_load_updates_serial_lsb, past, check_one_shift_outputs_loaded_msb, check_two_shifts_output_loaded_mid, check_three_shifts_wrap_to_loaded_lsb, check_zero_state_holds_one_idle_cycle, check_zero_state_holds_two_idle_cycles
bind shift_register shift_register_sva auto_sva_inst (
    .clk(clk),
    .reset(reset),
    .load(load),
    .load_data(load_data),
    .serial_out(serial_out)
);
