// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_reset_defaults, assert, property, h7ffffff, h7, check_adrmem_decode, disable, iff, h3, check_adrcfg_decode, h5, check_adr_low_bits_zero, check_adr_mapping, past, check_cmd_mapping, check_a1_inversion, check_config_read_address, check_memory_read_address, check_memory_read_bar_offset, h0, check_memory_read_byte_enable, check_config_read_byte_enable
bind pcidec_new pcidec_new_sva auto_sva_inst (
    .clk_i(clk_i),
    .nrst_i(nrst_i),
    .ad_i(ad_i),
    .cbe_i(cbe_i),
    .idsel_i(idsel_i),
    .bar0_i(bar0_i),
    .memEN_i(memEN_i),
    .pciadrLD_i(pciadrLD_i),
    .adrcfg_o(adrcfg_o),
    .adrmem_o(adrmem_o),
    .adr_o(adr_o),
    .cmd_o(cmd_o),
    .posedge(posedge),
    .b0(b0),
    .b1(b1),
    .b00(b00)
);
