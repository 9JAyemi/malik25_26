// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): clk, check_branch_flushD_equation, assert, property, posedge, check_branch_flushD_on_jmp_reg, check_branch_flushD_on_misprediction, check_branch_flushD_clear_without_cause, check_branch_flushE_equation, d0, check_branch_flushE_on_ex_dependency, check_branch_flushE_on_mem_dependency, check_branch_flushE_implies_valid_dependency, check_branch_flushE_clear_without_dependency
bind branch_hazard_detector branch_hazard_detector_sva auto_sva_inst (
    .ID_rs(ID_rs),
    .ID_rt(ID_rt),
    .EX_regwe(EX_regwe),
    .EX_RW(EX_RW),
    .MEM_ramtoreg(MEM_ramtoreg),
    .MEM_RW(MEM_RW),
    .ID_jmp_need_reg(ID_jmp_need_reg),
    .ID_jmp_reg(ID_jmp_reg),
    .ID_misprediction(ID_misprediction),
    .branch_flushD(branch_flushD),
    .branch_flushE(branch_flushE)
);
