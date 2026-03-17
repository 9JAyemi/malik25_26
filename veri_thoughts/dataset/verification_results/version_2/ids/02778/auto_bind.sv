// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_reset_clears_outputs, assert, property, posedge, b0, check_reset_holds_zero, past, check_first_cycle_after_reset_deassert, fell, check_serial_out_matches_msb, disable, iff, check_shift_update_full, check_msb_updates_from_bit30, check_lsb_captures_serial_in, check_middle_bits_shift, check_serial_out_from_prior_bit30
bind shift_register shift_register_sva auto_sva_inst (
    .clk(clk),
    .reset(reset),
    .serial_in(serial_in),
    .serial_out(serial_out),
    .parallel_out(parallel_out)
);
