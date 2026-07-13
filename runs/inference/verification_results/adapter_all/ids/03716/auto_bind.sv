// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_reset_clears_trace_outputs, assert, property, posedge, h0, check_read_captures_trace_outputs, disable, iff, past, check_write_captures_trace_outputs, check_wait_clears_trace_outputs, check_idle_holds_trace_outputs
bind limbus_cpu_cpu_nios2_oci_dtrace limbus_cpu_cpu_nios2_oci_dtrace_sva auto_sva_inst (
    .clk(clk),
    .jrst_n(jrst_n),
    .cpu_d_address(cpu_d_address),
    .cpu_d_read(cpu_d_read),
    .cpu_d_write(cpu_d_write),
    .cpu_d_wait(cpu_d_wait),
    .atm(atm),
    .dtm(dtm),
    .cpu_d_readdata(cpu_d_readdata),
    .cpu_d_writedata(cpu_d_writedata)
);
