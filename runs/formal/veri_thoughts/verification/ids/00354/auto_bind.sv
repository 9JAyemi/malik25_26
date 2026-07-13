// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_out_tied_low, assert, property, posedge, b0, check_count_d1_reg_zero, h00, check_wdata_captures_tx_fifo_on_ready, past, check_wdata_holds_when_not_ready
bind VerilogModule VerilogModule_sva auto_sva_inst (
    .out(out),
    .count_d1_reg(count_d1_reg),
    .m_axi_wdata(m_axi_wdata),
    .aclk(aclk),
    .s_dclk_o(s_dclk_o),
    .Q(Q),
    .m_axi_wready(m_axi_wready),
    .burst_count_reg(burst_count_reg),
    .tx_fifo_wr(tx_fifo_wr),
    .tx_fifowren_reg(tx_fifowren_reg),
    .tx_fifo_dataout_reg(tx_fifo_dataout_reg)
);
