// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): valid_next_high_when_load_high, assert, property, posedge, b1, valid_next_low_when_load_low, b0, valid_rise_follows_load_rise, rose, valid_fall_follows_load_fall, fell, out_cleared_next_on_no_load, b0000, clear_valid_and_out_on_load_fall, valid_low_implies_out_zero, four_cycle_load_delays_input_to_out, past, out_zero_on_valid_fall, valid_high_after_four_loads
bind shift_register shift_register_sva auto_sva_inst (
    .clk(clk),
    .in(in),
    .load(load),
    .out(out),
    .valid(valid)
);
