// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): clk, check_out_lo_matches_low_byte, assert, property, posedge, check_out_hi_matches_selected_byte, check_msb_clear_copies_low_byte_to_both_outputs, b0, check_msb_set_splits_high_and_low_bytes, b1, check_outputs_equal_when_msb_clear
bind decoder split_16bit_input_sva auto_sva_inst (
    .in(in),
    .out_hi(out_hi),
    .out_lo(out_lo)
);
