// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_cpu_d_address_passthrough, assert, property, posedge, disable, iff, check_cpu_d_read_passthrough, check_cpu_d_readdata_passthrough, check_cpu_d_writedata_passthrough, check_cpu_d_write_passthrough, check_cpu_d_wait_passthrough, check_dbrk_break_reset_low, b0, check_dbrk_break_stays_low, check_dbrk_goto0_low, check_dbrk_goto1_low, check_dbrk_traceme_low, check_dbrk_traceoff_low, check_dbrk_traceon_low, check_dbrk_trigout_low
bind niosii_nios2_gen2_0_cpu_nios2_oci_dbrk niosii_nios2_gen2_0_cpu_nios2_oci_dbrk_sva auto_sva_inst (
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
