// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_async_reset_clears_crc, assert, property, h00, check_sync_reset_clears_crc, disable, iff, check_sync_reset_priority_over_enable, check_crc_holds_when_disabled, past, check_crc_bit0_update, check_crc_bit1_update, check_crc_bit2_update, check_crc_upper_bits_shift
bind crc8_single_bit crc8_single_bit_sva auto_sva_inst (
    .data(data),
    .enable_crc(enable_crc),
    .reset(reset),
    .sync_reset_crc(sync_reset_crc),
    .clk(clk),
    .crc_out(crc_out),
    .posedge(posedge)
);
