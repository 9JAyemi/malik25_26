// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_wb_ctlout_pipeline, assert, property, posedge, disable, iff, initstate, past, check_m_ctlout_pipeline, check_add_result_pipeline, check_zero_pipeline, check_alu_result_pipeline, check_rdata2out_pipeline, check_five_bit_muxout_pipeline
bind EX_MEM EX_MEM_sva auto_sva_inst (
    .clk(clk),
    .ctlwb_out(ctlwb_out),
    .ctlm_out(ctlm_out),
    .adder_out(adder_out),
    .aluzero(aluzero),
    .aluout(aluout),
    .readdat2(readdat2),
    .muxout(muxout),
    .wb_ctlout(wb_ctlout),
    .m_ctlout(m_ctlout),
    .add_result(add_result),
    .zero(zero),
    .alu_result(alu_result),
    .rdata2out(rdata2out),
    .five_bit_muxout(five_bit_muxout)
);
