// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): reset_clears_regs, assert, property, posedge, b0, b00, hold_regs_on_stall, disable, iff, stable, capture_p_c_rfw, past, capture_p_c_wbsource, capture_p_alu_r, capture_p_rf_waddr, capture_p_jalra, capture_p_dout, comb_dmem_addr_passthrough, comb_dmem_drw_passthrough, comb_dmem_data_forward_mux, d0
bind cpu_mem cpu_mem_sva auto_sva_inst (
    .rst(rst),
    .clk(clk),
    .cpu_stall(cpu_stall),
    .ex_c_rfw(ex_c_rfw),
    .ex_c_wbsource(ex_c_wbsource),
    .ex_c_drw(ex_c_drw),
    .ex_alu_r(ex_alu_r),
    .ex_rfb(ex_rfb),
    .ex_rf_waddr(ex_rf_waddr),
    .ex_jalra(ex_jalra),
    .ex_rt(ex_rt),
    .wb_wdata(wb_wdata),
    .p_c_rfw(p_c_rfw),
    .p_c_wbsource(p_c_wbsource),
    .p_alu_r(p_alu_r),
    .dmem_data(dmem_data),
    .p_rf_waddr(p_rf_waddr),
    .p_jalra(p_jalra),
    .dmem_addr(dmem_addr),
    .dmem_drw(dmem_drw),
    .dmem_in(dmem_in),
    .p_dout(p_dout)
);
