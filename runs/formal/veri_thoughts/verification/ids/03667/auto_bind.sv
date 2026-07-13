// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_reset_clears_state, assert, property, posedge, b0, h0, check_conf_write_updates_working, disable, iff, past, check_working_holds_without_conf_write, check_working_increments_counter, d1, check_stopped_no_write_holds_counter, check_stopped_write_loads_low_half, check_stopped_write_masks_low_half, check_stopped_write_loads_high_half, check_stopped_write_masks_high_half
bind dps_main_counter dps_main_counter_sva auto_sva_inst (
    .iCLOCK(iCLOCK),
    .inRESET(inRESET),
    .iCONF_WRITE(iCONF_WRITE),
    .iCONF_ENA(iCONF_ENA),
    .iCOUNT_WRITE(iCOUNT_WRITE),
    .inCOUNT_DQM(inCOUNT_DQM),
    .iCOUNT_COUNTER(iCOUNT_COUNTER),
    .oWORKING(oWORKING),
    .oCOUNTER(oCOUNTER)
);
