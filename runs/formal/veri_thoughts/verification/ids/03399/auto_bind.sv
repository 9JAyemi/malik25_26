// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): ADD, b000000, NDU, b001000, ADC, b000010, ADZ, b000001, NDC, b001010, NDZ, b001001, LW, b0100, SW, b0101, check_f3_encoding, assert, property, global_clock, b00, d2, d3, check_non_store_zero, check_store_alu_match_forward, b0, check_store_load_match_forward, check_store_no_match_zero, check_f3_two_only_on_alu_forward, check_f3_three_only_on_load_forward, check_ccr_write_blocks_alu_forward, b1, check_f3_zero_only_without_forward_condition
bind forward_mem_stage forward_mem_stage_sva auto_sva_inst (
    .mem_wb_regA(mem_wb_regA),
    .mem_wb_regC(mem_wb_regC),
    .ex_mem_regA(ex_mem_regA),
    .mem_wb_op(mem_wb_op),
    .ex_mem_op(ex_mem_op),
    .mem_wb_CCR_write(mem_wb_CCR_write),
    .ex_mem_CCR_write(ex_mem_CCR_write),
    .F3(F3)
);
