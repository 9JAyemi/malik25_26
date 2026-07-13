// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): reset_outputs_zero, assert, property, posedge, d0, b0, check_writedata_update, disable, iff, past, check_address_update, check_read_update, check_readdata_update, check_wait_update, check_write_update, check_no_read_when_write, check_address_zero_when_not_write, check_address_matches_when_write, check_writedata_matches_when_write, check_writedata_matches_when_not_write, check_readdata_when_read, check_readdata_zero_when_no_read, check_dbrk_break_toggle_on_ack_low, check_dbrk_break_hold_on_ack_high, check_dbrk_static_zero
bind niosII_system_nios2_qsys_0_nios2_oci_dbrk niosII_system_nios2_qsys_0_nios2_oci_dbrk_sva auto_sva_inst (
    .E_st_data(E_st_data),
    .av_ld_data_aligned_filtered(av_ld_data_aligned_filtered),
    .clk(clk),
    .d_address(d_address),
    .d_read(d_read),
    .d_waitrequest(d_waitrequest),
    .d_write(d_write),
    .debugack(debugack),
    .reset_n(reset_n),
    .cpu_d_address(cpu_d_address),
    .cpu_d_read(cpu_d_read),
    .cpu_d_readdata(cpu_d_readdata),
    .cpu_d_wait(cpu_d_wait),
    .cpu_d_write(cpu_d_write),
    .cpu_d_writedata(cpu_d_writedata),
    .dbrk_break(dbrk_break),
    .dbrk_goto0(dbrk_goto0),
    .dbrk_goto1(dbrk_goto1),
    .dbrk_traceme(dbrk_traceme),
    .dbrk_traceoff(dbrk_traceoff),
    .dbrk_traceon(dbrk_traceon),
    .dbrk_trigout(dbrk_trigout)
);
