// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_rd_busy_constant_low, assert, property, posedge, disable, iff, b0, check_rd_mmu_flags_constant_zero, h000, check_rd_hit_constant_low, check_rd_data_constant_zero, h00000000, check_up_busy_constant_low, check_wr_busy_constant_low, check_rd_valid_clears_on_sync_reset_or_remove, check_rd_valid_sets_from_rd_req, b1, check_rd_valid_clears_from_rd_req_low, check_rd_valid_low_on_reset_release, rose
bind l1_data_cache_64entry_4way_line64b_bus_8b_disable_cache l1_data_cache_64entry_4way_line64b_bus_8b_disable_cache_sva auto_sva_inst (
    .iCLOCK(iCLOCK),
    .inRESET(inRESET),
    .iRESET_SYNC(iRESET_SYNC),
    .iREMOVE(iREMOVE),
    .iRD_REQ(iRD_REQ),
    .oRD_BUSY(oRD_BUSY),
    .iRD_ADDR(iRD_ADDR),
    .oRD_VALID(oRD_VALID),
    .oRD_HIT(oRD_HIT),
    .iRD_BUSY(iRD_BUSY),
    .oRD_DATA(oRD_DATA),
    .oRD_MMU_FLAGS(oRD_MMU_FLAGS),
    .iUP_REQ(iUP_REQ),
    .oUP_BUSY(oUP_BUSY),
    .iUP_ORDER(iUP_ORDER),
    .iUP_MASK(iUP_MASK),
    .iUP_ADDR(iUP_ADDR),
    .iUP_DATA(iUP_DATA),
    .iWR_REQ(iWR_REQ),
    .oWR_BUSY(oWR_BUSY),
    .iWR_ADDR(iWR_ADDR),
    .iWR_DATA(iWR_DATA),
    .iWR_MMU_FLAGS(iWR_MMU_FLAGS)
);
