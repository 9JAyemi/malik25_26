// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): shift_reg_update, assert, property, posedge, disable, iff, stable, shift_reg, parallel_load_update, serial_output_check, parallel_output_check, shift_direction_check, b0, shift_direction_check_2, shift_register_stable, parallel_load_stable, shift_direction_stable, shift_register_stable_2, parallel_load_stable_2, shift_direction_stable_2
bind shift_register shift_register_sva auto_sva_inst (
    .clk(clk),
    .shift_dir(shift_dir),
    .parallel_load(parallel_load),
    .data_in(data_in),
    .serial_out(serial_out),
    .parallel_out(parallel_out)
);
