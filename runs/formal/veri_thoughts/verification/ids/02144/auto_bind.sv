// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): reset_outputs_zero, assert, property, posedge, b00, check_forwardA_from_EXMEM, or, disable, iff, d0, b10, check_forwardA_from_MEMWB_no_EXMEM, b01, check_forwardA_default_zero, check_forwardA_EXMEM_priority, check_forwardA_code_space, b1, inside, check_forwardB_from_EXMEM, check_forwardB_from_MEMWB_no_EXMEM, check_forwardB_default_zero, check_forwardB_EXMEM_priority, check_forwardB_code_space
bind SwapUnit SwapUnit_sva auto_sva_inst (
    .rs(rs),
    .rt(rt),
    .rd(rd),
    .EXMEMregWrite(EXMEMregWrite),
    .EXMEMregisterRd(EXMEMregisterRd),
    .MEMWBregisterRd(MEMWBregisterRd),
    .MEMWBregWrite(MEMWBregWrite),
    .forwardB(forwardB),
    .forwardA(forwardA),
    .rst(rst)
);
