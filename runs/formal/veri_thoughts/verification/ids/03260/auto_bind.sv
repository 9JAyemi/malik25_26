// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_reset_clears_output_on_posedge, assert, property, h0000, check_reset_clears_output_on_negedge, check_load_copies_data_into_visible_upper_bits, disable, iff, past, check_load_shifts_prior_visible_bits_down, check_shift_rotates_visible_bits_when_not_loading, check_falling_edge_captures_d_into_output_lsb, b1
bind shift_register top_module_sva auto_sva_inst (
    .clk(clk),
    .reset(reset),
    .load(load),
    .data_in(data_in),
    .d(d),
    .q(q),
    .posedge(posedge),
    .negedge(negedge)
);
