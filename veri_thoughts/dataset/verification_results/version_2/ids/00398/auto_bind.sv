// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_init_q_low, assert, property, initstate, check_aclr_forces_zero, check_sclr_clears_q, disable, iff, check_sload_captures_zero, check_datain_captures_zero, check_ena_low_holds_zero, check_sclr_priority_over_sload, check_sload_priority_over_datain, check_datain_path_ignores_sdata
bind MISTRAL_FF MISTRAL_FF_sva auto_sva_inst (
    .DATAIN(DATAIN),
    .CLK(CLK),
    .ACLR(ACLR),
    .ENA(ENA),
    .SCLR(SCLR),
    .SLOAD(SLOAD),
    .SDATA(SDATA),
    .Q(Q),
    .posedge(posedge),
    .b0(b0)
);
