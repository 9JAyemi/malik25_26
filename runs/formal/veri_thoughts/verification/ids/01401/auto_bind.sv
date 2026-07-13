// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_parallel_load_next_out, assert, property, posedge, past, check_shift_lsb_zero_each_no_load, b0, check_shift_upper_bits_when_known, isunknown, check_two_no_loads_zero_lsb2, b00, check_three_no_loads_zero_lsb3, b000, check_four_no_loads_zero_all, b0000, check_load_then_shift_of_loaded_data, check_back_to_back_loads_last_wins, check_zero_sticky_without_load
bind shift_register shift_register_sva auto_sva_inst (
    .clk(clk),
    .load(load),
    .data_in(data_in),
    .data_out(data_out)
);
