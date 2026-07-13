// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_parallel_load_captures_data, assert, property, posedge, past, check_parallel_load_priority_over_shift, check_left_shift_rotates, b0, check_right_shift_rotates, check_serial_out_is_lsb, b1, check_left_shift_data_mapping, check_right_shift_data_mapping, check_left_shift_inserts_zero_msb, check_right_shift_inserts_zero_lsb
bind shift_register shift_register_sva auto_sva_inst (
    .clk(clk),
    .shift_dir(shift_dir),
    .parallel_load(parallel_load),
    .data_in(data_in),
    .serial_out(serial_out),
    .parallel_out(parallel_out)
);
