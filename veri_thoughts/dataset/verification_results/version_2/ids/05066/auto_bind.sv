// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_reset_cmd_default, assert, property, b0111, check_reset_cfg_clear, check_reset_mem_clear, check_reset_addr_upper_default, h1fffff, check_adr_lowbit_from_cbe, disable, iff, check_cfg_decode_requires_cfg_cmd, check_mem_decode_requires_enable_and_mem_cmd, check_cmd_capture_on_load, past, check_cmd_hold_without_load, check_addr_upper_capture_on_load, check_addr_upper_hold_without_load, check_cfg_decode_after_load, check_mem_decode_after_load
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
    .b101(b101),
    .b011(b011),
    .b00(b00)
);
