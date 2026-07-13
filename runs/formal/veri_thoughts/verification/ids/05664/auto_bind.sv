// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_reset_clears_shift_reg, assert, property, b0000, check_load_captures_data, disable, iff, past, check_enable_rotates_shift_reg, check_idle_holds_shift_reg, check_select0_decode, check_select1_decode, check_shifted_data_value, b00, check_data_out_on_load, check_data_out_shifted_path, check_data_out_register_path
bind top_module top_module_sva auto_sva_inst (
    .clk(clk),
    .reset(reset),
    .load(load),
    .ena(ena),
    .data_in(data_in),
    .data_out(data_out),
    .shift_reg(shift_reg),
    .select(select),
    .shifted_data(shifted_data),
    .posedge(posedge)
);
