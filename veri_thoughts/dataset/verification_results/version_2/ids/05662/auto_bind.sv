// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_reset_clears_register, assert, property, posedge, h00, check_load_captures_parallel_in, disable, iff, past, check_load_priority_over_shift, check_shift_left_zero_fill, b0, check_default_captures_data_in
bind shift_register shift_register_sva auto_sva_inst (
    .clk(clk),
    .reset(reset),
    .load(load),
    .shift(shift),
    .data_in(data_in),
    .parallel_in(parallel_in),
    .data_out(data_out)
);
