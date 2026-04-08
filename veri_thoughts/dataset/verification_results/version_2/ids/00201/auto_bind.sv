// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_mb_reset_definition, assert, property, posedge, disable, iff, b0, check_mb_reset_on_debug_reset, check_mb_reset_on_ext_reset, check_mb_reset_on_dcm_unlock, check_mb_reset_clear_condition, check_bus_struct_reset_definition, check_peripheral_reset_definition, check_interconnect_aresetn_definition, check_peripheral_aresetn_definition
bind zynq_reset zynq_reset_sva auto_sva_inst (
    .slowest_sync_clk(slowest_sync_clk),
    .ext_reset_in(ext_reset_in),
    .aux_reset_in(aux_reset_in),
    .mb_debug_sys_rst(mb_debug_sys_rst),
    .dcm_locked(dcm_locked),
    .mb_reset(mb_reset),
    .bus_struct_reset(bus_struct_reset),
    .peripheral_reset(peripheral_reset),
    .interconnect_aresetn(interconnect_aresetn),
    .peripheral_aresetn(peripheral_aresetn)
);
