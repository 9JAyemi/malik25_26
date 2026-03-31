// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_reg_wr_en_implies_reg_en, assert, property, posedge, disable, iff, check_reset_release_clears_outputs, rose, check_wr_rise_generates_single_pulse, check_rd_rise_generates_reg_en, check_reg_wr_en_single_cycle, check_reg_wr_en_history_decode, past, check_reg_en_history_decode
bind dmi_jtag_to_core_sync dmi_jtag_to_core_sync_sva auto_sva_inst (
    .rd_en(rd_en),
    .wr_en(wr_en),
    .rst_n(rst_n),
    .clk(clk),
    .reg_en(reg_en),
    .reg_wr_en(reg_wr_en)
);
