// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): register_data, counter_data, reset_state, assert, property, posedge, b0000, hFF, check_register_load, disable, iff, past, check_register_hold, check_counter_increment, d1, check_counter_hold, check_output_is_xor, check_output_upper_nibble, hF, check_output_lower_nibble, check_output_next_reg_load_only, check_output_next_counter_only, check_output_next_both, check_output_hold_when_idle
bind register_counter_xor register_counter_xor_sva auto_sva_inst (
    .clk(clk),
    .reset(reset),
    .reg_data_in(reg_data_in),
    .reg_load(reg_load),
    .counter_enable(counter_enable),
    .output_data(output_data)
);
