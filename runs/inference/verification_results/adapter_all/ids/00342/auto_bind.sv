// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_parallel_out_update, assert, property, posedge, b1, past, b0, check_serial_out_from_prev_parallel, check_parallel_load_captures_data, check_serial_load_captures_data, check_shift_left_updates_parallel, check_shift_right_updates_parallel, check_serial_out_matches_parallel_lsb, check_left_then_right_restores_parallel, check_right_then_left_restores_parallel
bind shift_register shift_register_sva auto_sva_inst (
    .clk(clk),
    .shift_dir(shift_dir),
    .parallel_load(parallel_load),
    .data_in(data_in),
    .serial_out(serial_out),
    .parallel_out(parallel_out)
);
