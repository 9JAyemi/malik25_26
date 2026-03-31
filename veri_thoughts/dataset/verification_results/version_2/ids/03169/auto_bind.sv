// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_counter_load_zero_extend, assert, property, disable, iff, b000, past, check_counter_increment, d1, check_counter_decrement, check_shift_clear_on_load, check_shift_shift_behavior, check_parallel_load_data_capture, check_parallel_load_data_hold, check_ripple_counter_out_tracks_counter, b1, check_ser_out_mapping, check_counter_zero_after_reset, initstate, check_top_regs_zero_after_reset
bind top_module top_module_sva auto_sva_inst (
    .clk(clk),
    .reset(reset),
    .up_down(up_down),
    .parallel_load(parallel_load),
    .LOAD_IN(LOAD_IN),
    .ripple_counter_out(ripple_counter_out),
    .ser_out(ser_out),
    .parallel_load_data(parallel_load_data),
    .ripple_counter(ripple_counter),
    .shift_register_data(shift_register_data),
    .posedge(posedge),
    .b0(b0)
);
