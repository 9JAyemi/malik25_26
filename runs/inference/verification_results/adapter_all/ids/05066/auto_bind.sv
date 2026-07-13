// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_reset_defaults, assert, property, h7ffffff, h7, check_adr_o_mapping, disable, iff, past, check_cmd_o_mapping, check_adrmem_o_decode, check_adrcfg_o_decode, check_adrmem_o_requires_memen, check_adrmem_o_requires_bar_match, check_adrmem_o_requires_zero_lsb, check_adrmem_o_requires_cmd_code, check_adrcfg_o_requires_idsel, check_adrcfg_o_requires_zero_lsb, check_adrcfg_o_requires_cmd_code
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
    .adr(adr),
    .cmd(cmd),
    .b1(b1),
    .b00(b00),
    .b011(b011),
    .b101(b101)
);
