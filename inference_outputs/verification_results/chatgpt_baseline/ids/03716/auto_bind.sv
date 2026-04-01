// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_reset_clears_outputs, assert, property, posedge, b0, check_read_captures_addr_and_data, disable, iff, past, check_write_captures_addr_and_data, check_wait_clears_outputs, check_idle_holds_outputs, check_read_has_priority_over_write_or_wait, check_write_has_priority_over_wait
bind limbus_cpu_cpu_nios2_oci_dtrace limbus_cpu_cpu_nios2_oci_dtrace_sva auto_sva_inst (
    .clk(clk),
    .cpu_d_address(cpu_d_address),
    .cpu_d_read(cpu_d_read),
    .cpu_d_readdata(cpu_d_readdata),
    .cpu_d_wait(cpu_d_wait),
    .cpu_d_write(cpu_d_write),
    .cpu_d_writedata(cpu_d_writedata),
    .jrst_n(jrst_n),
    .trc_ctrl(trc_ctrl),
    .atm(atm),
    .dtm(dtm)
);
