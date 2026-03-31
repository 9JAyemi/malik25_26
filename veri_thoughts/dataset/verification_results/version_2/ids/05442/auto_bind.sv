// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_next_state_function, assert, property, posedge, b1, past, check_load_captures_parallel_in, check_shift_right_updates_register, check_shift_left_updates_register, check_shift_right_inserts_serial_in, check_shift_right_moves_data, check_shift_left_inserts_serial_in, check_shift_left_moves_data
bind shift_register shift_register_sva auto_sva_inst (
    .clk(clk),
    .load(load),
    .shift_dir(shift_dir),
    .parallel_in(parallel_in),
    .serial_in(serial_in),
    .serial_out(serial_out)
);
