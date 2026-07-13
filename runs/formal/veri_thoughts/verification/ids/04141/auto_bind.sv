// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_async_reset_clears_outputs, assert, property, posedge, b0, h0, check_sync_reset_clears_outputs, disable, iff, check_gr_capture_on_valid, b1, past, check_gr_hold_without_write, stable, check_spr_capture_from_wb, check_spr_capture_from_auto, check_spr_forward_current_data, check_frcr_capture_from_wb, check_frcr_forward_current_data
bind execute_forwarding_register execute_forwarding_register_sva auto_sva_inst (
    .iCLOCK(iCLOCK),
    .inRESET(inRESET),
    .iRESET_SYNC(iRESET_SYNC),
    .iWB_GR_VALID(iWB_GR_VALID),
    .iWB_GR_DATA(iWB_GR_DATA),
    .iWB_GR_DEST(iWB_GR_DEST),
    .iWB_GR_DEST_SYSREG(iWB_GR_DEST_SYSREG),
    .iWB_SPR_VALID(iWB_SPR_VALID),
    .iWB_SPR_DATA(iWB_SPR_DATA),
    .iWB_AUTO_SPR_VALID(iWB_AUTO_SPR_VALID),
    .iWB_AUTO_SPR_DATA(iWB_AUTO_SPR_DATA),
    .iCUUR_SPR_DATA(iCUUR_SPR_DATA),
    .iWB_FRCR_VALID(iWB_FRCR_VALID),
    .iWB_FRCR_DATA(iWB_FRCR_DATA),
    .iCUUR_FRCR_DATA(iCUUR_FRCR_DATA),
    .oFDR_GR_VALID(oFDR_GR_VALID),
    .oFDR_GR_DATA(oFDR_GR_DATA),
    .oFDR_GR_DEST(oFDR_GR_DEST),
    .oFDR_GR_DEST_SYSREG(oFDR_GR_DEST_SYSREG),
    .oFDR_SPR_VALID(oFDR_SPR_VALID),
    .oFDR_SPR_DATA(oFDR_SPR_DATA),
    .oFDR_FRCR_VALID(oFDR_FRCR_VALID),
    .oFDR_FRCR_DATA(oFDR_FRCR_DATA)
);
