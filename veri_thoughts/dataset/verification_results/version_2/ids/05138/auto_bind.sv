// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): clk, check_por_inversion, assert, property, posedge, disable, iff, b0, check_pad_up_function, check_pad_dn_l_function, check_bsr_up_mirror, check_bsr_dn_l_mirror, check_to_core_mux_function, check_to_core_bsr_path, check_to_core_rcvr_path, check_outputs_when_oe_low, check_outputs_when_oe_high
bind bw_io_cmos_edgelogic bw_io_cmos_edgelogic_sva auto_sva_inst (
    .data(data),
    .oe(oe),
    .bsr_mode(bsr_mode),
    .por_l(por_l),
    .bsr_data_to_core(bsr_data_to_core),
    .se(se),
    .rcvr_data(rcvr_data),
    .pad_up(pad_up),
    .pad_dn_l(pad_dn_l),
    .bsr_up(bsr_up),
    .bsr_dn_l(bsr_dn_l),
    .por(por),
    .to_core(to_core)
);
