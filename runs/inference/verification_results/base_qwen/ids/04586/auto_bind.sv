// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): iUP_BUSY, iWR_BUSY, property, p_req_valid, posedge, disable, iff, b_req_valid, endproperty, assert, else, error, Request, validation, failed, p_req_busy, busy, handling, p_rd_valid, Read, valid, p_rd_hit, hit, p_rd_data, h0, data, p_up_busy, Update, p_wr_busy, Write, p_req_removal, b0, removal, p_reset, Reset, p_reset_sync, synchronization
bind l1_data_cache_64entry_4way_line64b_bus_8b_disable_cache l1_data_cache_64entry_4way_line64b_bus_8b_disable_cache_sva auto_sva_inst (
    .iCLOCK(iCLOCK),
    .inRESET(inRESET),
    .iRESET_SYNC(iRESET_SYNC),
    .iREMOVE(iREMOVE),
    .iRD_REQ(iRD_REQ),
    .iRD_BUSY(iRD_BUSY),
    .iRD_ADDR(iRD_ADDR),
    .iUP_REQ(iUP_REQ),
    .iUP_ORDER(iUP_ORDER),
    .iUP_MASK(iUP_MASK),
    .iUP_ADDR(iUP_ADDR),
    .iUP_DATA(iUP_DATA),
    .iWR_REQ(iWR_REQ),
    .iWR_ADDR(iWR_ADDR),
    .iWR_DATA(iWR_DATA),
    .iWR_MMU_FLAGS(iWR_MMU_FLAGS),
    .oRD_BUSY(oRD_BUSY),
    .oRD_VALID(oRD_VALID),
    .oRD_HIT(oRD_HIT),
    .oRD_DATA(oRD_DATA),
    .oUP_BUSY(oUP_BUSY),
    .oWR_BUSY(oWR_BUSY)
);
