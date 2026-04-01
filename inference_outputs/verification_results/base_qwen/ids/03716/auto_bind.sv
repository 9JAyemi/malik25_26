// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): reset, assert, property, posedge, b0, read_operation, disable, iff, write_operation, wait_operation, exclusive_access, no_change, update_only_during_operations, update_only_during_operations_2, update_only_during_operations_3, update_only_during_operations_4, update_only_during_operations_5
bind limbus_cpu_cpu_nios2_oci_dtrace limbus_cpu_cpu_nios2_oci_dtrace_sva auto_sva_inst (
    .clk(clk),
    .jrst_n(jrst_n),
    .cpu_d_read(cpu_d_read),
    .cpu_d_write(cpu_d_write),
    .cpu_d_wait(cpu_d_wait),
    .atm(atm),
    .dtm(dtm),
    .cpu_d_address(cpu_d_address),
    .cpu_d_readdata(cpu_d_readdata),
    .cpu_d_writedata(cpu_d_writedata)
);
