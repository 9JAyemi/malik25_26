// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): generate, if, C_HAS_SOFTECC_OUTPUT_REGS_B, begin, gen_no_output_stage, check_dout_passthrough, assert, property, posedge, check_rdaddrecc_passthrough, check_sbiterr_passthrough, check_dbiterr_passthrough, end, endgenerate, gen_has_output_stage, check_dout_registered, b1, past, check_rdaddrecc_registered, check_sbiterr_registered, check_dbiterr_registered
bind mem_soft_ecc mem_soft_ecc_sva auto_sva_inst (
    .CLK(CLK),
    .C_DATA_WIDTH(C_DATA_WIDTH),
    .DIN(DIN),
    .DOUT(DOUT),
    .SBITERR_IN(SBITERR_IN),
    .DBITERR_IN(DBITERR_IN),
    .SBITERR(SBITERR),
    .DBITERR(DBITERR),
    .C_ADDRB_WIDTH(C_ADDRB_WIDTH),
    .RDADDRECC_IN(RDADDRECC_IN),
    .RDADDRECC(RDADDRECC)
);
