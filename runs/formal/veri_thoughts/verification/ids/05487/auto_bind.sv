// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): DATA_REAY, idle_count, idle_count_flag, state_count, state_count_flag, data_count, data_count_flag, bitcount, state, DATA, DATA_BUF, IDLE, b00, GUIDANCE, b01, DATAREAD, b10, IDLE_HIGH_DUR, d262143, GUIDE_LOW_DUR, d230000, GUIDE_HIGH_DUR, d210000, DATA_HIGH_DUR, d41500, BIT_AVAILABLE_DUR, d20000, reset_values_check, assert, property, posedge, d0, b0, ready_output_mirror_check, disable, iff, idle_flag_set_check, idle_flag_clear_check, idle_count_increment_check, past, d1, idle_count_clear_check, guidance_flag_set_check, guidance_flag_clear_check, state_count_increment_check, state_count_clear_check, idle_to_guidance_check, idle_hold_check, guidance_to_dataread_check, guidance_hold_check, dataread_to_idle_check, d33, dataread_hold_check, illegal_state_return_check, b11, data_flag_set_check, data_flag_clear_check, data_count_increment_check, data_count_clear_check, bitcount_reset_outside_dataread_check, bitcount_increment_check, bitcount_hold_check, data_clear_outside_dataread_check, ready_set_check, d32, ready_clear_check, odata_load_check, odata_hold_check
bind IRDA_RECEIVE_Terasic IRDA_RECEIVE_Terasic_sva auto_sva_inst (
    .iCLK(iCLK),
    .iRST_n(iRST_n),
    .iIRDA(iIRDA),
    .iREAD(iREAD),
    .oDATA_REAY(oDATA_REAY),
    .oDATA(oDATA)
);
