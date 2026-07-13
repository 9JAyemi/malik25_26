// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): reset_clears_readdata, assert, property, posedge, h0000_0000, reset_release_holds_zero_one_cycle, rose, map_prev_addr0_to_const0, disable, iff, past, b0, h560F_6F0F, map_prev_addr1_to_const1, b1, hADC3_C2C2, next_cycle_update_addr0, next_cycle_update_addr1, stable_when_address_unchanged, readdata_changes_when_addr_changed_prev, readdata_nonzero_for_legal_prev_addr
bind address_decoder address_decoder_sva auto_sva_inst (
    .address(address),
    .clock(clock),
    .reset_n(reset_n),
    .readdata(readdata)
);
