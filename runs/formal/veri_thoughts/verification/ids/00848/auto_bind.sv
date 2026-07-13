// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): DATA_WIDTH, check_dataout_mux_function, assert, property, posedge, disable, iff, check_dataout_sel_register_settings, check_dataout_sel_datain, check_valid_passthrough, check_stall_passthrough, check_dataout_stable_when_all_inputs_stable, stable, check_valid_stable_when_input_valid_stable, check_stall_stable_when_input_stall_stable, check_independence_unselected_datain, changed, check_independence_unselected_regsettings
bind vfabric_bypass_reg vfabric_bypass_reg_sva auto_sva_inst (
    .clock(clock),
    .resetn(resetn),
    .i_settings(i_settings),
    .i_register_settings(i_register_settings),
    .i_datain(i_datain),
    .i_datain_valid(i_datain_valid),
    .o_datain_stall(o_datain_stall),
    .o_dataout(o_dataout),
    .o_dataout_valid(o_dataout_valid),
    .i_dataout_stall(i_dataout_stall)
);
