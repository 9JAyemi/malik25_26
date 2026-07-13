// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): b1, check_forwardA_equation, assert, property, global_clock, b10, b00, check_forwardB_equation, check_forwardA_valid_encoding, check_forwardB_valid_encoding, check_forwardA_exmem_match_sets_forward, check_forwardA_memwb_match_sets_forward, check_forwardA_no_match_clears_forward, check_forwardB_exmem_match_sets_forward, check_forwardB_memwb_match_sets_forward, check_forwardB_no_match_clears_forward
bind forwarding_unit forwarding_unit_sva auto_sva_inst (
    .rt_addr_IDEX(rt_addr_IDEX),
    .rs_addr_IDEX(rs_addr_IDEX),
    .rd_addr_EXMEM(rd_addr_EXMEM),
    .rd_addr_MEMWB(rd_addr_MEMWB),
    .regwrite_EXMEM(regwrite_EXMEM),
    .regwrite_MEMWB(regwrite_MEMWB),
    .forwardA(forwardA),
    .forwardB(forwardB),
    .rs_from_mem(rs_from_mem),
    .rt_from_mem(rt_from_mem),
    .rs_from_ex(rs_from_ex),
    .rt_from_ex(rt_from_ex),
    .assign(assign)
);
