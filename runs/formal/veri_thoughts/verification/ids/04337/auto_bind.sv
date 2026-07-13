// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): pipeline, check_serial_out_matches_pipeline2, assert, property, posedge, check_pipeline2_captures_serial_in, b1, b000, past, check_pipeline2_upper_bits_zero, check_pipeline1_captures_pipeline2, check_pipeline0_loads_data_in, check_pipeline0_shifts_pipeline1, check_pipeline0_selected_source, check_serial_out_tracks_serial_in
bind shift_register shift_register_sva auto_sva_inst (
    .clk(clk),
    .parallel_load(parallel_load),
    .serial_in(serial_in),
    .serial_out(serial_out),
    .data_in(data_in)
);
