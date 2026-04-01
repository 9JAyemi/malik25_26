// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): DATA_WIDTH, check_output_mux_function, assert, property, posedge, disable, iff, check_valid_passthrough, check_stall_passthrough, check_select_register_settings, check_select_datain, check_valid_high_when_datain_valid, check_valid_low_when_datain_invalid, check_stall_high_when_dataout_stall, check_stall_low_when_dataout_not_stall
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
