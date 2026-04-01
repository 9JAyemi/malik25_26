// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_e_matches_valid_and_full, assert, property, posedge, disable, iff, b0, b1, ram_full_fb_i_reg, check_wready_tied_low, check_ram_full_fb_i_reg_0_matches_e, check_e_requires_valid, check_e_requires_full, check_full_requires_e, check_full_requires_valid, check_full_requires_ram_full_fb_i_reg_0, check_e_low_clears_full, check_e_low_clears_ram_full_fb_i_reg_0, check_valid_without_full_sets_e_low, check_valid_without_ram_full_fb_i_reg_0_sets_e_low
bind system_auto_cc_0_wr_status_flags_as_16 system_auto_cc_0_wr_status_flags_as_16_sva auto_sva_inst (
    .ram_full_fb_i_reg_0(ram_full_fb_i_reg_0),
    .E(E),
    .s_axi_wready(s_axi_wready),
    .gic0_gc0_count_d1_reg_3(gic0_gc0_count_d1_reg_3),
    .s_aclk(s_aclk),
    .out(out),
    .s_axi_wvalid(s_axi_wvalid),
    .Q(Q),
    .gnxpm_cdc_rd_pntr_bin_reg_3(gnxpm_cdc_rd_pntr_bin_reg_3)
);
