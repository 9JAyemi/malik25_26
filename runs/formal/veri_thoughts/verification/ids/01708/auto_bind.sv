// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): capture_mem_control_wb, assert, property, posedge, past, capture_Read_data, capture_mem_ALU_result, capture_mem_Write_reg, stable_propagation_mem_control_wb, stable, stable_propagation_Read_data, stable_propagation_mem_ALU_result, stable_propagation_mem_Write_reg, change_propagation_mem_control_wb, changed, change_propagation_Read_data, change_propagation_mem_ALU_result, change_propagation_mem_Write_reg
bind MEM_WB MEM_WB_sva auto_sva_inst (
    .clk(clk),
    .control_wb_in(control_wb_in),
    .Read_data_in(Read_data_in),
    .ALU_result_in(ALU_result_in),
    .Write_reg_in(Write_reg_in),
    .mem_control_wb(mem_control_wb),
    .Read_data(Read_data),
    .mem_ALU_result(mem_ALU_result),
    .mem_Write_reg(mem_Write_reg)
);
