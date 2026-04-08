// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_serial_out_mapping, assert, property, posedge, b0, check_parallel_load_updates_register, past, check_parallel_load_updates_serial, check_left_shift_updates_register, check_left_shift_clears_serial_out, h00, check_right_shift_updates_register, check_right_shift_updates_serial
bind shift_register shift_register_sva auto_sva_inst (
    .clk(clk),
    .shift_dir(shift_dir),
    .parallel_load(parallel_load),
    .data_in(data_in),
    .serial_out(serial_out),
    .parallel_out(parallel_out)
);
