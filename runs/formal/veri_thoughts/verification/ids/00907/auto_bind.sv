// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): return_adr, IEN_reg, IRQ_reg, I, check_irq_reg_captures_IRQ, assert, property, posedge, check_IEN_reg_cleared_on_interrupt, b1, b0, check_IEN_reg_cleared_on_IOF_only, check_IEN_reg_set_on_IEN_only, check_return_adr_captured_on_interrupt, check_branch_ISR_definition, check_ISR_adr_on_interrupt, h001, check_ISR_adr_on_RTI_only, check_ISR_default_when_no_event, h000, check_branch_zero_implies_zero_addr, check_I_high_requires_inputs, check_I_low_when_IEN_reg_zero, check_I_low_when_IRQ_reg_zero, check_I_low_when_branch_d_one
bind interrupt interrupt_sva auto_sva_inst (
    .clock(clock),
    .IEN_d(IEN_d),
    .IOF_d(IOF_d),
    .RTI_d(RTI_d),
    .branch_d(branch_d),
    .IRQ(IRQ),
    .PC(PC),
    .branch_ISR(branch_ISR),
    .ISR_adr(ISR_adr)
);
