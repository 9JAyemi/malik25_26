// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_parallel_out_registered, assert, property, posedge, b1, past, check_serial_out_matches_lsb, check_parallel_load_updates_register, check_parallel_load_priority, check_left_shift_update, b0, check_right_shift_update
bind shift_register shift_register_sva auto_sva_inst (
    .clk(clk),
    .shift_dir(shift_dir),
    .parallel_load(parallel_load),
    .data_in(data_in),
    .serial_out(serial_out),
    .parallel_out(parallel_out)
);
