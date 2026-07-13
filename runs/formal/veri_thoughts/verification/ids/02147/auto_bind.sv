// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_outputs_follow_reset_req, assert, property, posedge, disable, iff, initstate, past, check_outputs_one_when_reset_req, check_outputs_zero_when_no_reset_req, check_all_outputs_equal, check_outputs_rise_together, rose, check_outputs_fall_together, fell, check_reset_req_rise_causes_output_rise, check_reset_req_fall_causes_output_fall, check_stable_inputs_imply_stable_outputs, stable
bind processor_system_reset processor_system_reset_sva auto_sva_inst (
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
