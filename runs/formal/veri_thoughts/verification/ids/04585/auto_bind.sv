// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_wb_read_data_load, assert, property, disable, iff, past, check_wb_read_data_hold, check_wb_alu_data_load, check_wb_alu_data_hold, check_wb_gpr_wa_load, check_wb_gpr_wa_hold, check_wb_mem_to_gpr_select_load, check_wb_mem_to_gpr_select_hold, check_wb_gpr_we_hold, check_wb_gpr_we_clear_on_mem_stall_or_flush, check_wb_gpr_we_load
bind musb_memwb_register musb_memwb_register_sva auto_sva_inst (
    .clk(clk),
    .rst(rst),
    .mem_read_data(mem_read_data),
    .mem_alu_data(mem_alu_data),
    .mem_gpr_wa(mem_gpr_wa),
    .mem_mem_to_gpr_select(mem_mem_to_gpr_select),
    .mem_gpr_we(mem_gpr_we),
    .mem_flush(mem_flush),
    .mem_stall(mem_stall),
    .wb_stall(wb_stall),
    .wb_read_data(wb_read_data),
    .wb_alu_data(wb_alu_data),
    .wb_gpr_wa(wb_gpr_wa),
    .wb_mem_to_gpr_select(wb_mem_to_gpr_select),
    .wb_gpr_we(wb_gpr_we),
    .posedge(posedge),
    .b0(b0)
);
