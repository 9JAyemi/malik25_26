// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): reg_data, reset_clears_reg, assert, property, posedge, b0, reset_forces_busout_low, check_busout_mux_eq, check_busout_high_requires_enable, b1, check_busout_high_requires_data, check_busout_change_caused_by_inputs, changed, check_busout_stable_when_inputs_stable, stable, check_write_captures_bus_in, disable, iff, past, check_hold_without_write, check_busout_stable_when_enabled_and_no_write, check_busout_tracks_reg_when_enabled
bind Register Register_sva auto_sva_inst (
    .Bus_in(Bus_in),
    .clk(clk),
    .reset(reset),
    .r_in(r_in),
    .r_out(r_out),
    .Bus_out(Bus_out)
);
