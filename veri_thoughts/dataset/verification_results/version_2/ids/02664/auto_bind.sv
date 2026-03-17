// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): reg_data, hold_outputs_during_load, assert, property, posedge, past, b1, load_updates_reg_data, hold_reg_data_when_not_load, compute_passthrough_reg_data, b00, compute_invert_reg_data, b01, compute_passthrough_data_in, b10, compute_invert_data_in, b11, valid_high_on_operation, load_then_ctrl00_uses_loaded_data, load_then_ctrl01_uses_inverted_loaded_data, load_then_ctrl10_uses_next_data_in, load_then_ctrl11_uses_inverted_next_data_in
bind control_unit control_unit_sva auto_sva_inst (
    .ctrl(ctrl),
    .data_in(data_in),
    .load(load),
    .clk(clk),
    .data_out(data_out),
    .valid(valid)
);
