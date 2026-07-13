// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_reset_clears_state, assert, property, h000001, h7, check_adr_o_matches_state, disable, iff, check_cmd_o_matches_state, check_adrmem_o_constant_low, check_adrcfg_o_constant_low, check_state_holds_without_load, past, check_state_updates_on_load
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
    .b1(b1)
);
