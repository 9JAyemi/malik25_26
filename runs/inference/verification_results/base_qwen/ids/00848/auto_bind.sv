// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): bypass_reg_1, assert, property, posedge, disable, iff, b1, bypass_reg_2, b0, bypass_reg_3, bypass_reg_4, reset_1, reset_2, bypass_reg_5, bypass_reg_6, bypass_reg_7, bypass_reg_8, bypass_reg_9, bypass_reg_10
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
