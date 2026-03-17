// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_se_equals_gse, assert, property, posedge, disable, iff, check_testmode_l_inverse, check_mem_bypass_def, check_sehold_def, check_mem_write_disable_def, check_mux_drive_disable_def, check_so0_mux, check_so1_mux, check_so2_mux, check_testmode_blocks_mem_bypass, b0, check_shift_disables_sehold, check_memw_implies_mux_disable
bind scan_chain_interface scan_chain_interface_sva auto_sva_inst (
    .ctu_tst_pre_grst_l(ctu_tst_pre_grst_l),
    .arst_l(arst_l),
    .global_shift_enable(global_shift_enable),
    .ctu_tst_scan_disable(ctu_tst_scan_disable),
    .ctu_tst_scanmode(ctu_tst_scanmode),
    .ctu_tst_macrotest(ctu_tst_macrotest),
    .ctu_tst_short_chain(ctu_tst_short_chain),
    .long_chain_so_0(long_chain_so_0),
    .short_chain_so_0(short_chain_so_0),
    .long_chain_so_1(long_chain_so_1),
    .short_chain_so_1(short_chain_so_1),
    .long_chain_so_2(long_chain_so_2),
    .short_chain_so_2(short_chain_so_2),
    .mux_drive_disable(mux_drive_disable),
    .mem_write_disable(mem_write_disable),
    .sehold(sehold),
    .se(se),
    .testmode_l(testmode_l),
    .mem_bypass(mem_bypass),
    .so_0(so_0),
    .so_1(so_1),
    .so_2(so_2)
);
